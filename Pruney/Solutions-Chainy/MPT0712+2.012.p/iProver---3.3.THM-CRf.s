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
% DateTime   : Thu Dec  3 11:52:46 EST 2020

% Result     : Theorem 43.74s
% Output     : CNFRefutation 43.74s
% Verified   : 
% Statistics : Number of formulae       :  234 (1105 expanded)
%              Number of clauses        :  176 ( 630 expanded)
%              Number of leaves         :   22 ( 317 expanded)
%              Depth                    :   14
%              Number of atoms          :  606 (2672 expanded)
%              Number of equality atoms :  284 (1369 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f31])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f58,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f53,f55,f55])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f50,f54,f54])).

fof(f52,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_324,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_322,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_136394,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_324,c_322])).

cnf(c_331,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_136678,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(X2),X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_136394,c_331])).

cnf(c_8,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_152048,plain,
    ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_136678,c_8])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1458,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_324,c_322])).

cnf(c_9,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1482,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_1458,c_9])).

cnf(c_1493,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(X2),X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1458,c_331])).

cnf(c_12906,plain,
    ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0)
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(resolution,[status(thm)],[c_1493,c_8])).

cnf(c_157301,plain,
    ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_152048,c_3,c_1482,c_12906])).

cnf(c_323,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_136371,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_323,c_322])).

cnf(c_136367,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_323,c_8])).

cnf(c_138287,plain,
    ( X0 = k2_relat_1(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136371,c_136367])).

cnf(c_152092,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136678,c_138287])).

cnf(c_157590,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | X0 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_157301,c_152092])).

cnf(c_158138,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(k1_xboole_0)),X0) ),
    inference(resolution,[status(thm)],[c_157590,c_9])).

cnf(c_138738,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138287,c_136394])).

cnf(c_1790,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_323,c_322])).

cnf(c_1784,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_323,c_8])).

cnf(c_2754,plain,
    ( X0 = k2_relat_1(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1790,c_1784])).

cnf(c_3190,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2754,c_1458])).

cnf(c_1478,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_1458,c_8])).

cnf(c_1496,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1478,c_3])).

cnf(c_6620,plain,
    ( r1_tarski(X0,X1)
    | X0 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3190,c_1496])).

cnf(c_140531,plain,
    ( r1_tarski(X0,X1)
    | X0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_138738,c_6620])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_140559,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_140531,c_0])).

cnf(c_7180,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_6620,c_0])).

cnf(c_7569,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7180,c_3])).

cnf(c_7570,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_7569])).

cnf(c_141505,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_140559,c_3,c_7180])).

cnf(c_141506,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_141505])).

cnf(c_136388,plain,
    ( r1_tarski(X0,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_324,c_8])).

cnf(c_137263,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_136388,c_0])).

cnf(c_141662,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_141506,c_137263])).

cnf(c_158435,plain,
    ( ~ r1_tarski(X0,k1_relat_1(k1_relat_1(k1_xboole_0)))
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_158138,c_141662])).

cnf(c_2741,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1790,c_8])).

cnf(c_1778,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution,[status(thm)],[c_323,c_0])).

cnf(c_9646,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2741,c_1778])).

cnf(c_15709,plain,
    ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12906,c_3,c_1482])).

cnf(c_12970,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1493,c_2754])).

cnf(c_15985,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | X0 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_15709,c_12970])).

cnf(c_17992,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(k1_xboole_0)),X0) ),
    inference(resolution,[status(thm)],[c_15985,c_9])).

cnf(c_1446,plain,
    ( r1_tarski(X0,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_324,c_8])).

cnf(c_2325,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | r1_tarski(X1,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1446,c_0])).

cnf(c_7583,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_relat_1(k1_xboole_0))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7570,c_2325])).

cnf(c_18223,plain,
    ( ~ r1_tarski(X0,k1_relat_1(k1_relat_1(k1_xboole_0)))
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_17992,c_7583])).

cnf(c_138276,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_136371,c_8])).

cnf(c_329,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_136372,plain,
    ( X0 != X1
    | X2 != k2_relat_1(X1)
    | k2_relat_1(X0) = X2 ),
    inference(resolution,[status(thm)],[c_323,c_329])).

cnf(c_147452,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138276,c_136372])).

cnf(c_158153,plain,
    ( r1_tarski(k1_relat_1(k2_relat_1(X0)),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_157590,c_147452])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_52,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_56,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_203,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_16])).

cnf(c_204,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_208,plain,
    ( ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ r2_hidden(X0,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_17])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ r2_hidden(X1,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_211,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_325,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_334,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_650,plain,
    ( ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_773,plain,
    ( k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_669,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_787,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_674,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_786,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_862,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
    | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_863,plain,
    ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_184,plain,
    ( r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k2_enumset1(X0,X0,X0,X0) != X4
    | k7_relat_1(k7_relat_1(X2,X4),X3) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_185,plain,
    ( r2_hidden(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,k2_enumset1(X0,X0,X0,X0)),X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_679,plain,
    ( r2_hidden(X0,X1)
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),X1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(c_794,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(X1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_1000,plain,
    ( r2_hidden(X0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1002,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_851,plain,
    ( ~ r1_tarski(X0,k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1261,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_1262,plain,
    ( r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_598,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_597,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_599,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1014,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_597,c_599])).

cnf(c_1428,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_598,c_1014])).

cnf(c_1222,plain,
    ( X0 != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(X0) = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_1703,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_710,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,X0))
    | k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1704,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_778,plain,
    ( X0 != X1
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_975,plain,
    ( X0 != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_1221,plain,
    ( k2_relat_1(X0) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(X0)
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_1964,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_327,plain,
    ( X0 != X1
    | X2 != X3
    | k7_relat_1(X0,X2) = k7_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_953,plain,
    ( X0 != X1
    | X2 != sK1
    | k7_relat_1(X2,X0) = k7_relat_1(sK1,X1) ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1547,plain,
    ( X0 != X1
    | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,X1)
    | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_953])).

cnf(c_1923,plain,
    ( X0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_2220,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_645,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2483,plain,
    ( v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_857,plain,
    ( X0 != X1
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != X1
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1276,plain,
    ( X0 != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_3957,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_1219,plain,
    ( X0 != X1
    | X0 = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_4703,plain,
    ( X0 != k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
    | X0 = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_4771,plain,
    ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_3424,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_6986,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3424])).

cnf(c_4015,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1778,c_8])).

cnf(c_11417,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k2_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4015,c_3])).

cnf(c_9643,plain,
    ( X0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_2741,c_323])).

cnf(c_11741,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_11417,c_9643])).

cnf(c_11833,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11741,c_1790])).

cnf(c_1791,plain,
    ( X0 != X1
    | X2 != k2_relat_1(X1)
    | k2_relat_1(X0) = X2 ),
    inference(resolution,[status(thm)],[c_323,c_329])).

cnf(c_9675,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2741,c_1791])).

cnf(c_10392,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9675,c_6620])).

cnf(c_12161,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k2_relat_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_11833,c_10392])).

cnf(c_12295,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12161,c_15])).

cnf(c_1408,plain,
    ( X0 != X1
    | X0 = k7_relat_1(k7_relat_1(sK1,X2),X3)
    | k7_relat_1(k7_relat_1(sK1,X2),X3) != X1 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_3066,plain,
    ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(k7_relat_1(sK1,X2)))
    | X0 != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(k7_relat_1(sK1,X2))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_6119,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1))) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3066])).

cnf(c_16211,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6119])).

cnf(c_4802,plain,
    ( X0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_16213,plain,
    ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_4802])).

cnf(c_994,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(X1,X2))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1586,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_24541,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ v1_relat_1(sK1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_3064,plain,
    ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(sK1))
    | X0 != k1_xboole_0
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_28942,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3064])).

cnf(c_28945,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28942])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1113,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
    | r2_hidden(X0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_43632,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r2_hidden(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_7482,plain,
    ( X0 != k1_xboole_0
    | k2_relat_1(X0) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_24432,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1))) != k1_xboole_0
    | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1)))) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7482])).

cnf(c_58464,plain,
    ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0
    | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_24432])).

cnf(c_66448,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3243,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(k7_relat_1(sK1,X2),X3),X4)
    | X4 != X1
    | k7_relat_1(k7_relat_1(sK1,X2),X3) != X0 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_7994,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),X1)
    | ~ r1_tarski(k1_xboole_0,X2)
    | X1 != X2
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3243])).

cnf(c_66467,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ r1_tarski(k1_xboole_0,X1)
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
    inference(instantiation,[status(thm)],[c_7994])).

cnf(c_101458,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_66467])).

cnf(c_101460,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_101458])).

cnf(c_1267,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2)
    | X2 != X1
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_28943,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),X1)
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2)
    | X2 != X1
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_68677,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),X1)
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
    inference(instantiation,[status(thm)],[c_28943])).

cnf(c_101680,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_68677])).

cnf(c_101682,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_101680])).

cnf(c_135568,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relat_1(sK1,X2),X3)
    | X3 != X1
    | k7_relat_1(sK1,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_137643,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1)
    | X1 != X0
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_135568])).

cnf(c_142376,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_137643])).

cnf(c_133503,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | X2 != X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_135561,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r1_tarski(X1,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | X1 != X0
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_133503])).

cnf(c_142320,plain,
    ( r1_tarski(X0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | X0 != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_135561])).

cnf(c_145603,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_142320])).

cnf(c_139152,plain,
    ( X0 != X1
    | X0 = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
    | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != X1 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_140423,plain,
    ( X0 != k2_relat_1(X1)
    | X0 = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
    | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_139152])).

cnf(c_157242,plain,
    ( X0 = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
    | X0 != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_140423])).

cnf(c_141123,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1)
    | X1 != X0
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_135568])).

cnf(c_166412,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
    | X0 != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_141123])).

cnf(c_167105,plain,
    ( X0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_158153,c_17,c_15,c_52,c_56,c_211,c_334,c_650,c_773,c_787,c_862,c_863,c_1002,c_1261,c_1262,c_1428,c_1703,c_1704,c_1964,c_2220,c_2483,c_2754,c_3957,c_4703,c_4771,c_6986,c_12295,c_16211,c_16213,c_24541,c_28945,c_43632,c_58464,c_66448,c_101460,c_101682,c_142376,c_145603,c_157242,c_166412])).

cnf(c_167111,plain,
    ( ~ r1_tarski(X0,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_158435,c_17,c_15,c_3,c_52,c_56,c_211,c_334,c_650,c_773,c_787,c_862,c_863,c_1002,c_1261,c_1262,c_1428,c_1478,c_1703,c_1704,c_1964,c_2220,c_2483,c_2754,c_3957,c_4703,c_4771,c_6986,c_9646,c_12295,c_16211,c_16213,c_18223,c_24541,c_28945,c_43632,c_58464,c_66448,c_101460,c_101682,c_142376,c_145603,c_157242,c_166412])).

cnf(c_167135,plain,
    ( $false ),
    inference(resolution,[status(thm)],[c_167111,c_1])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 43.74/5.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.74/5.99  
% 43.74/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.74/5.99  
% 43.74/5.99  ------  iProver source info
% 43.74/5.99  
% 43.74/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.74/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.74/5.99  git: non_committed_changes: false
% 43.74/5.99  git: last_make_outside_of_git: false
% 43.74/5.99  
% 43.74/5.99  ------ 
% 43.74/5.99  ------ Parsing...
% 43.74/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.74/5.99  
% 43.74/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 43.74/5.99  
% 43.74/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.74/5.99  
% 43.74/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.74/5.99  ------ Proving...
% 43.74/5.99  ------ Problem Properties 
% 43.74/5.99  
% 43.74/5.99  
% 43.74/5.99  clauses                                 15
% 43.74/5.99  conjectures                             2
% 43.74/5.99  EPR                                     4
% 43.74/5.99  Horn                                    14
% 43.74/5.99  unary                                   6
% 43.74/5.99  binary                                  3
% 43.74/5.99  lits                                    31
% 43.74/5.99  lits eq                                 7
% 43.74/5.99  fd_pure                                 0
% 43.74/5.99  fd_pseudo                               0
% 43.74/5.99  fd_cond                                 0
% 43.74/5.99  fd_pseudo_cond                          1
% 43.74/5.99  AC symbols                              0
% 43.74/5.99  
% 43.74/5.99  ------ Input Options Time Limit: Unbounded
% 43.74/5.99  
% 43.74/5.99  
% 43.74/5.99  ------ 
% 43.74/5.99  Current options:
% 43.74/5.99  ------ 
% 43.74/5.99  
% 43.74/5.99  
% 43.74/5.99  
% 43.74/5.99  
% 43.74/5.99  ------ Proving...
% 43.74/5.99  
% 43.74/5.99  
% 43.74/5.99  % SZS status Theorem for theBenchmark.p
% 43.74/5.99  
% 43.74/5.99   Resolution empty clause
% 43.74/5.99  
% 43.74/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.74/5.99  
% 43.74/5.99  fof(f10,axiom,(
% 43.74/5.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f45,plain,(
% 43.74/5.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 43.74/5.99    inference(cnf_transformation,[],[f10])).
% 43.74/5.99  
% 43.74/5.99  fof(f2,axiom,(
% 43.74/5.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f36,plain,(
% 43.74/5.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f2])).
% 43.74/5.99  
% 43.74/5.99  fof(f44,plain,(
% 43.74/5.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 43.74/5.99    inference(cnf_transformation,[],[f10])).
% 43.74/5.99  
% 43.74/5.99  fof(f1,axiom,(
% 43.74/5.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f27,plain,(
% 43.74/5.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.74/5.99    inference(nnf_transformation,[],[f1])).
% 43.74/5.99  
% 43.74/5.99  fof(f28,plain,(
% 43.74/5.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.74/5.99    inference(flattening,[],[f27])).
% 43.74/5.99  
% 43.74/5.99  fof(f35,plain,(
% 43.74/5.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f28])).
% 43.74/5.99  
% 43.74/5.99  fof(f14,conjecture,(
% 43.74/5.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f15,negated_conjecture,(
% 43.74/5.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 43.74/5.99    inference(negated_conjecture,[],[f14])).
% 43.74/5.99  
% 43.74/5.99  fof(f25,plain,(
% 43.74/5.99    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 43.74/5.99    inference(ennf_transformation,[],[f15])).
% 43.74/5.99  
% 43.74/5.99  fof(f26,plain,(
% 43.74/5.99    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 43.74/5.99    inference(flattening,[],[f25])).
% 43.74/5.99  
% 43.74/5.99  fof(f31,plain,(
% 43.74/5.99    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 43.74/5.99    introduced(choice_axiom,[])).
% 43.74/5.99  
% 43.74/5.99  fof(f32,plain,(
% 43.74/5.99    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0))) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 43.74/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f31])).
% 43.74/5.99  
% 43.74/5.99  fof(f51,plain,(
% 43.74/5.99    v1_relat_1(sK1)),
% 43.74/5.99    inference(cnf_transformation,[],[f32])).
% 43.74/5.99  
% 43.74/5.99  fof(f53,plain,(
% 43.74/5.99    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k1_tarski(sK0))),k1_tarski(k1_funct_1(sK1,sK0)))),
% 43.74/5.99    inference(cnf_transformation,[],[f32])).
% 43.74/5.99  
% 43.74/5.99  fof(f3,axiom,(
% 43.74/5.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f37,plain,(
% 43.74/5.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f3])).
% 43.74/5.99  
% 43.74/5.99  fof(f4,axiom,(
% 43.74/5.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f38,plain,(
% 43.74/5.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f4])).
% 43.74/5.99  
% 43.74/5.99  fof(f5,axiom,(
% 43.74/5.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f39,plain,(
% 43.74/5.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f5])).
% 43.74/5.99  
% 43.74/5.99  fof(f54,plain,(
% 43.74/5.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 43.74/5.99    inference(definition_unfolding,[],[f38,f39])).
% 43.74/5.99  
% 43.74/5.99  fof(f55,plain,(
% 43.74/5.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 43.74/5.99    inference(definition_unfolding,[],[f37,f54])).
% 43.74/5.99  
% 43.74/5.99  fof(f58,plain,(
% 43.74/5.99    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))),
% 43.74/5.99    inference(definition_unfolding,[],[f53,f55,f55])).
% 43.74/5.99  
% 43.74/5.99  fof(f33,plain,(
% 43.74/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 43.74/5.99    inference(cnf_transformation,[],[f28])).
% 43.74/5.99  
% 43.74/5.99  fof(f60,plain,(
% 43.74/5.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 43.74/5.99    inference(equality_resolution,[],[f33])).
% 43.74/5.99  
% 43.74/5.99  fof(f13,axiom,(
% 43.74/5.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f23,plain,(
% 43.74/5.99    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 43.74/5.99    inference(ennf_transformation,[],[f13])).
% 43.74/5.99  
% 43.74/5.99  fof(f24,plain,(
% 43.74/5.99    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 43.74/5.99    inference(flattening,[],[f23])).
% 43.74/5.99  
% 43.74/5.99  fof(f50,plain,(
% 43.74/5.99    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f24])).
% 43.74/5.99  
% 43.74/5.99  fof(f57,plain,(
% 43.74/5.99    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 43.74/5.99    inference(definition_unfolding,[],[f50,f54,f54])).
% 43.74/5.99  
% 43.74/5.99  fof(f52,plain,(
% 43.74/5.99    v1_funct_1(sK1)),
% 43.74/5.99    inference(cnf_transformation,[],[f32])).
% 43.74/5.99  
% 43.74/5.99  fof(f12,axiom,(
% 43.74/5.99    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f22,plain,(
% 43.74/5.99    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 43.74/5.99    inference(ennf_transformation,[],[f12])).
% 43.74/5.99  
% 43.74/5.99  fof(f49,plain,(
% 43.74/5.99    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f22])).
% 43.74/5.99  
% 43.74/5.99  fof(f8,axiom,(
% 43.74/5.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f18,plain,(
% 43.74/5.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 43.74/5.99    inference(ennf_transformation,[],[f8])).
% 43.74/5.99  
% 43.74/5.99  fof(f42,plain,(
% 43.74/5.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f18])).
% 43.74/5.99  
% 43.74/5.99  fof(f34,plain,(
% 43.74/5.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 43.74/5.99    inference(cnf_transformation,[],[f28])).
% 43.74/5.99  
% 43.74/5.99  fof(f59,plain,(
% 43.74/5.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 43.74/5.99    inference(equality_resolution,[],[f34])).
% 43.74/5.99  
% 43.74/5.99  fof(f6,axiom,(
% 43.74/5.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f16,plain,(
% 43.74/5.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 43.74/5.99    inference(ennf_transformation,[],[f6])).
% 43.74/5.99  
% 43.74/5.99  fof(f40,plain,(
% 43.74/5.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f16])).
% 43.74/5.99  
% 43.74/5.99  fof(f56,plain,(
% 43.74/5.99    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 43.74/5.99    inference(definition_unfolding,[],[f40,f55])).
% 43.74/5.99  
% 43.74/5.99  fof(f9,axiom,(
% 43.74/5.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f19,plain,(
% 43.74/5.99    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 43.74/5.99    inference(ennf_transformation,[],[f9])).
% 43.74/5.99  
% 43.74/5.99  fof(f20,plain,(
% 43.74/5.99    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 43.74/5.99    inference(flattening,[],[f19])).
% 43.74/5.99  
% 43.74/5.99  fof(f43,plain,(
% 43.74/5.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f20])).
% 43.74/5.99  
% 43.74/5.99  fof(f7,axiom,(
% 43.74/5.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f17,plain,(
% 43.74/5.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 43.74/5.99    inference(ennf_transformation,[],[f7])).
% 43.74/5.99  
% 43.74/5.99  fof(f41,plain,(
% 43.74/5.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f17])).
% 43.74/5.99  
% 43.74/5.99  fof(f11,axiom,(
% 43.74/5.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 43.74/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/5.99  
% 43.74/5.99  fof(f21,plain,(
% 43.74/5.99    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 43.74/5.99    inference(ennf_transformation,[],[f11])).
% 43.74/5.99  
% 43.74/5.99  fof(f29,plain,(
% 43.74/5.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 43.74/5.99    inference(nnf_transformation,[],[f21])).
% 43.74/5.99  
% 43.74/5.99  fof(f30,plain,(
% 43.74/5.99    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 43.74/5.99    inference(flattening,[],[f29])).
% 43.74/5.99  
% 43.74/5.99  fof(f47,plain,(
% 43.74/5.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 43.74/5.99    inference(cnf_transformation,[],[f30])).
% 43.74/5.99  
% 43.74/5.99  cnf(c_324,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.74/5.99      theory(equality) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_322,plain,( X0 = X0 ),theory(equality) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_136394,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_324,c_322]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_331,plain,
% 43.74/5.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 43.74/5.99      theory(equality) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_136678,plain,
% 43.74/5.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 43.74/5.99      | r1_tarski(k1_relat_1(X2),X1)
% 43.74/5.99      | X2 != X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_136394,c_331]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_8,plain,
% 43.74/5.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 43.74/5.99      inference(cnf_transformation,[],[f45]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_152048,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0)
% 43.74/5.99      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_136678,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_3,plain,
% 43.74/5.99      ( r1_tarski(k1_xboole_0,X0) ),
% 43.74/5.99      inference(cnf_transformation,[],[f36]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1458,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_324,c_322]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_9,plain,
% 43.74/5.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 43.74/5.99      inference(cnf_transformation,[],[f44]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1482,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~ r1_tarski(k1_xboole_0,X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1458,c_9]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1493,plain,
% 43.74/5.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 43.74/5.99      | r1_tarski(k1_relat_1(X2),X1)
% 43.74/5.99      | X2 != X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1458,c_331]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_12906,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0)
% 43.74/5.99      | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1493,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_157301,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0) ),
% 43.74/5.99      inference(global_propositional_subsumption,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_152048,c_3,c_1482,c_12906]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_323,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_136371,plain,
% 43.74/5.99      ( X0 != X1 | X1 = X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_323,c_322]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_136367,plain,
% 43.74/5.99      ( X0 != k1_xboole_0 | k2_relat_1(k1_xboole_0) = X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_323,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_138287,plain,
% 43.74/5.99      ( X0 = k2_relat_1(k1_xboole_0) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_136371,c_136367]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_152092,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(X0),X1)
% 43.74/5.99      | ~ r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1)
% 43.74/5.99      | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_136678,c_138287]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_157590,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(X0),X1) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(backward_subsumption_resolution,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_157301,c_152092]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_158138,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k1_relat_1(k1_xboole_0)),X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_157590,c_9]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_138738,plain,
% 43.74/5.99      ( r1_tarski(X0,X1)
% 43.74/5.99      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
% 43.74/5.99      | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_138287,c_136394]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1790,plain,
% 43.74/5.99      ( X0 != X1 | X1 = X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_323,c_322]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1784,plain,
% 43.74/5.99      ( X0 != k1_xboole_0 | k2_relat_1(k1_xboole_0) = X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_323,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_2754,plain,
% 43.74/5.99      ( X0 = k2_relat_1(k1_xboole_0) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1790,c_1784]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_3190,plain,
% 43.74/5.99      ( r1_tarski(X0,X1)
% 43.74/5.99      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
% 43.74/5.99      | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_2754,c_1458]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1478,plain,
% 43.74/5.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~ r1_tarski(k1_xboole_0,X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1458,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1496,plain,
% 43.74/5.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
% 43.74/5.99      inference(global_propositional_subsumption,[status(thm)],[c_1478,c_3]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_6620,plain,
% 43.74/5.99      ( r1_tarski(X0,X1) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(forward_subsumption_resolution,[status(thm)],[c_3190,c_1496]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_140531,plain,
% 43.74/5.99      ( r1_tarski(X0,X1) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(global_propositional_subsumption,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_138738,c_6620]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_0,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 43.74/5.99      inference(cnf_transformation,[],[f35]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_140559,plain,
% 43.74/5.99      ( r1_tarski(X0,X1)
% 43.74/5.99      | ~ r1_tarski(X0,k1_xboole_0)
% 43.74/5.99      | ~ r1_tarski(k1_xboole_0,X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_140531,c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_7180,plain,
% 43.74/5.99      ( r1_tarski(X0,X1)
% 43.74/5.99      | ~ r1_tarski(X0,k1_xboole_0)
% 43.74/5.99      | ~ r1_tarski(k1_xboole_0,X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_6620,c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_7569,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1) ),
% 43.74/5.99      inference(global_propositional_subsumption,[status(thm)],[c_7180,c_3]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_7570,plain,
% 43.74/5.99      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k1_xboole_0) ),
% 43.74/5.99      inference(renaming,[status(thm)],[c_7569]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_141505,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1) ),
% 43.74/5.99      inference(global_propositional_subsumption,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_140559,c_3,c_7180]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_141506,plain,
% 43.74/5.99      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k1_xboole_0) ),
% 43.74/5.99      inference(renaming,[status(thm)],[c_141505]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_136388,plain,
% 43.74/5.99      ( r1_tarski(X0,k2_relat_1(k1_xboole_0))
% 43.74/5.99      | ~ r1_tarski(X1,k1_xboole_0)
% 43.74/5.99      | X0 != X1 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_324,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_137263,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | ~ r1_tarski(X1,X0)
% 43.74/5.99      | r1_tarski(X1,k2_relat_1(k1_xboole_0))
% 43.74/5.99      | ~ r1_tarski(X0,k1_xboole_0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_136388,c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_141662,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | r1_tarski(X0,k2_relat_1(k1_xboole_0))
% 43.74/5.99      | ~ r1_tarski(X1,k1_xboole_0) ),
% 43.74/5.99      inference(backward_subsumption_resolution,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_141506,c_137263]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_158435,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_relat_1(k1_relat_1(k1_xboole_0)))
% 43.74/5.99      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_158138,c_141662]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_2741,plain,
% 43.74/5.99      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1790,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1778,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X2 != X0 | X1 = X2 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_323,c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_9646,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k2_relat_1(k1_xboole_0))
% 43.74/5.99      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
% 43.74/5.99      | X0 = k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_2741,c_1778]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_15709,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X0) ),
% 43.74/5.99      inference(global_propositional_subsumption,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_12906,c_3,c_1482]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_12970,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(X0),X1)
% 43.74/5.99      | ~ r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),X1)
% 43.74/5.99      | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1493,c_2754]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_15985,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(X0),X1) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(backward_subsumption_resolution,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_15709,c_12970]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_17992,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k1_relat_1(k1_xboole_0)),X0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_15985,c_9]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1446,plain,
% 43.74/5.99      ( r1_tarski(X0,k2_relat_1(k1_xboole_0))
% 43.74/5.99      | ~ r1_tarski(X1,k1_xboole_0)
% 43.74/5.99      | X0 != X1 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_324,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_2325,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | ~ r1_tarski(X1,X0)
% 43.74/5.99      | r1_tarski(X1,k2_relat_1(k1_xboole_0))
% 43.74/5.99      | ~ r1_tarski(X0,k1_xboole_0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1446,c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_7583,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | r1_tarski(X0,k2_relat_1(k1_xboole_0))
% 43.74/5.99      | ~ r1_tarski(X1,k1_xboole_0) ),
% 43.74/5.99      inference(backward_subsumption_resolution,[status(thm)],[c_7570,c_2325]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_18223,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_relat_1(k1_relat_1(k1_xboole_0)))
% 43.74/5.99      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_17992,c_7583]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_138276,plain,
% 43.74/5.99      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_136371,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_329,plain,
% 43.74/5.99      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 43.74/5.99      theory(equality) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_136372,plain,
% 43.74/5.99      ( X0 != X1 | X2 != k2_relat_1(X1) | k2_relat_1(X0) = X2 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_323,c_329]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_147452,plain,
% 43.74/5.99      ( X0 != k1_xboole_0 | k2_relat_1(X0) = k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_138276,c_136372]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_158153,plain,
% 43.74/5.99      ( r1_tarski(k1_relat_1(k2_relat_1(X0)),X1) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_157590,c_147452]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_17,negated_conjecture,
% 43.74/5.99      ( v1_relat_1(sK1) ),
% 43.74/5.99      inference(cnf_transformation,[],[f51]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_15,negated_conjecture,
% 43.74/5.99      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))) ),
% 43.74/5.99      inference(cnf_transformation,[],[f58]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f60]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_52,plain,
% 43.74/5.99      ( r1_tarski(sK0,sK0) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_2]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_56,plain,
% 43.74/5.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_14,plain,
% 43.74/5.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 43.74/5.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 43.74/5.99      | ~ v1_funct_1(X1)
% 43.74/5.99      | ~ v1_relat_1(X1)
% 43.74/5.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2)) ),
% 43.74/5.99      inference(cnf_transformation,[],[f57]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_16,negated_conjecture,
% 43.74/5.99      ( v1_funct_1(sK1) ),
% 43.74/5.99      inference(cnf_transformation,[],[f52]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_203,plain,
% 43.74/5.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 43.74/5.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 43.74/5.99      | ~ v1_relat_1(X1)
% 43.74/5.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X2)) = k9_relat_1(X1,k2_enumset1(X0,X0,X0,X2))
% 43.74/5.99      | sK1 != X1 ),
% 43.74/5.99      inference(resolution_lifted,[status(thm)],[c_14,c_16]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_204,plain,
% 43.74/5.99      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 43.74/5.99      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 43.74/5.99      inference(unflattening,[status(thm)],[c_203]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_208,plain,
% 43.74/5.99      ( ~ r2_hidden(X1,k1_relat_1(sK1))
% 43.74/5.99      | ~ r2_hidden(X0,k1_relat_1(sK1))
% 43.74/5.99      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 43.74/5.99      inference(global_propositional_subsumption,[status(thm)],[c_204,c_17]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_209,plain,
% 43.74/5.99      ( ~ r2_hidden(X0,k1_relat_1(sK1))
% 43.74/5.99      | ~ r2_hidden(X1,k1_relat_1(sK1))
% 43.74/5.99      | k2_enumset1(k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X1),k1_funct_1(sK1,X0)) = k9_relat_1(sK1,k2_enumset1(X1,X1,X1,X0)) ),
% 43.74/5.99      inference(renaming,[status(thm)],[c_208]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_211,plain,
% 43.74/5.99      ( ~ r2_hidden(sK0,k1_relat_1(sK1))
% 43.74/5.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_209]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_325,plain,
% 43.74/5.99      ( X0 != X1
% 43.74/5.99      | X2 != X3
% 43.74/5.99      | X4 != X5
% 43.74/5.99      | X6 != X7
% 43.74/5.99      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 43.74/5.99      theory(equality) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_334,plain,
% 43.74/5.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK0)
% 43.74/5.99      | sK0 != sK0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_325]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_13,plain,
% 43.74/5.99      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 43.74/5.99      inference(cnf_transformation,[],[f49]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_650,plain,
% 43.74/5.99      ( ~ v1_relat_1(sK1) | k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_13]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_773,plain,
% 43.74/5.99      ( k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_322]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_6,plain,
% 43.74/5.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 43.74/5.99      inference(cnf_transformation,[],[f42]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_669,plain,
% 43.74/5.99      ( ~ v1_relat_1(sK1)
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_6]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_787,plain,
% 43.74/5.99      ( ~ v1_relat_1(sK1)
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_669]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_674,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 43.74/5.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X1
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_324]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_786,plain,
% 43.74/5.99      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 43.74/5.99      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 43.74/5.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != X0
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_674]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_862,plain,
% 43.74/5.99      ( ~ r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | r1_tarski(k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)))
% 43.74/5.99      | k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_786]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f59]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_863,plain,
% 43.74/5.99      ( r1_tarski(k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k9_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_4,plain,
% 43.74/5.99      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 43.74/5.99      inference(cnf_transformation,[],[f56]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_7,plain,
% 43.74/5.99      ( ~ r1_xboole_0(X0,X1)
% 43.74/5.99      | ~ v1_relat_1(X2)
% 43.74/5.99      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 43.74/5.99      inference(cnf_transformation,[],[f43]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_184,plain,
% 43.74/5.99      ( r2_hidden(X0,X1)
% 43.74/5.99      | ~ v1_relat_1(X2)
% 43.74/5.99      | X3 != X1
% 43.74/5.99      | k2_enumset1(X0,X0,X0,X0) != X4
% 43.74/5.99      | k7_relat_1(k7_relat_1(X2,X4),X3) = k1_xboole_0 ),
% 43.74/5.99      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_185,plain,
% 43.74/5.99      ( r2_hidden(X0,X1)
% 43.74/5.99      | ~ v1_relat_1(X2)
% 43.74/5.99      | k7_relat_1(k7_relat_1(X2,k2_enumset1(X0,X0,X0,X0)),X1) = k1_xboole_0 ),
% 43.74/5.99      inference(unflattening,[status(thm)],[c_184]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_679,plain,
% 43.74/5.99      ( r2_hidden(X0,X1)
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),X1) = k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_185]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_794,plain,
% 43.74/5.99      ( r2_hidden(X0,k1_relat_1(X1))
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(X1)) = k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_679]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1000,plain,
% 43.74/5.99      ( r2_hidden(X0,k1_relat_1(sK1))
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_794]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1002,plain,
% 43.74/5.99      ( r2_hidden(sK0,k1_relat_1(sK1))
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1000]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_851,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1261,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_851]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1262,plain,
% 43.74/5.99      ( r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_598,plain,
% 43.74/5.99      ( r1_tarski(X0,X0) = iProver_top ),
% 43.74/5.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_597,plain,
% 43.74/5.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 43.74/5.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_599,plain,
% 43.74/5.99      ( X0 = X1
% 43.74/5.99      | r1_tarski(X0,X1) != iProver_top
% 43.74/5.99      | r1_tarski(X1,X0) != iProver_top ),
% 43.74/5.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1014,plain,
% 43.74/5.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 43.74/5.99      inference(superposition,[status(thm)],[c_597,c_599]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1428,plain,
% 43.74/5.99      ( k1_xboole_0 = k1_xboole_0 ),
% 43.74/5.99      inference(superposition,[status(thm)],[c_598,c_1014]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1222,plain,
% 43.74/5.99      ( X0 != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k2_relat_1(X0) = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_329]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1703,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1222]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_710,plain,
% 43.74/5.99      ( ~ v1_relat_1(k7_relat_1(sK1,X0))
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_13]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1704,plain,
% 43.74/5.99      ( ~ v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_710]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_778,plain,
% 43.74/5.99      ( X0 != X1
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_323]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_975,plain,
% 43.74/5.99      ( X0 != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = X0
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_778]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1221,plain,
% 43.74/5.99      ( k2_relat_1(X0) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(X0)
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_975]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1964,plain,
% 43.74/5.99      ( k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1221]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_327,plain,
% 43.74/5.99      ( X0 != X1 | X2 != X3 | k7_relat_1(X0,X2) = k7_relat_1(X1,X3) ),
% 43.74/5.99      theory(equality) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_953,plain,
% 43.74/5.99      ( X0 != X1 | X2 != sK1 | k7_relat_1(X2,X0) = k7_relat_1(sK1,X1) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_327]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1547,plain,
% 43.74/5.99      ( X0 != X1
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,X1)
% 43.74/5.99      | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_953]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1923,plain,
% 43.74/5.99      ( X0 != k2_enumset1(sK0,sK0,sK0,sK0)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),X0) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1547]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_2220,plain,
% 43.74/5.99      ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k7_relat_1(sK1,k1_relat_1(sK1)) != sK1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1923]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_5,plain,
% 43.74/5.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 43.74/5.99      inference(cnf_transformation,[],[f41]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_645,plain,
% 43.74/5.99      ( v1_relat_1(k7_relat_1(sK1,X0)) | ~ v1_relat_1(sK1) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_5]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_2483,plain,
% 43.74/5.99      ( v1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | ~ v1_relat_1(sK1) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_645]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_857,plain,
% 43.74/5.99      ( X0 != X1
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != X1
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_323]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1276,plain,
% 43.74/5.99      ( X0 != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_857]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_3957,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1276]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1219,plain,
% 43.74/5.99      ( X0 != X1
% 43.74/5.99      | X0 = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_323]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_4703,plain,
% 43.74/5.99      ( X0 != k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
% 43.74/5.99      | X0 = k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1219]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_4771,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1276]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_3424,plain,
% 43.74/5.99      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_323]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_6986,plain,
% 43.74/5.99      ( X0 != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_3424]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_4015,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 43.74/5.99      | ~ r1_tarski(k1_xboole_0,X0)
% 43.74/5.99      | X0 = k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_1778,c_8]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_11417,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(global_propositional_subsumption,[status(thm)],[c_4015,c_3]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_9643,plain,
% 43.74/5.99      ( X0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_2741,c_323]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_11741,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_11417,c_9643]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_11833,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_11741,c_1790]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1791,plain,
% 43.74/5.99      ( X0 != X1 | X2 != k2_relat_1(X1) | k2_relat_1(X0) = X2 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_323,c_329]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_9675,plain,
% 43.74/5.99      ( X0 != k1_xboole_0 | k2_relat_1(X0) = k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_2741,c_1791]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_10392,plain,
% 43.74/5.99      ( r1_tarski(k2_relat_1(X0),X1) | X0 != k1_xboole_0 ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_9675,c_6620]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_12161,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(k2_relat_1(X0),X1) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_11833,c_10392]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_12295,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_12161,c_15]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1408,plain,
% 43.74/5.99      ( X0 != X1
% 43.74/5.99      | X0 = k7_relat_1(k7_relat_1(sK1,X2),X3)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,X2),X3) != X1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_323]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_3066,plain,
% 43.74/5.99      ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(k7_relat_1(sK1,X2)))
% 43.74/5.99      | X0 != k1_xboole_0
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(k7_relat_1(sK1,X2))) != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1408]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_6119,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1))) != k1_xboole_0
% 43.74/5.99      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1)))
% 43.74/5.99      | k1_xboole_0 != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_3066]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_16211,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0
% 43.74/5.99      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k1_xboole_0 != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_6119]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_4802,plain,
% 43.74/5.99      ( X0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = X0
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_857]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_16213,plain,
% 43.74/5.99      ( k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 43.74/5.99      | k1_xboole_0 != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_4802]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_994,plain,
% 43.74/5.99      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(X1,X2))) = k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_794]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1586,plain,
% 43.74/5.99      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1))) = k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_994]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_24541,plain,
% 43.74/5.99      ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | ~ v1_relat_1(sK1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) = k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1586]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_3064,plain,
% 43.74/5.99      ( X0 = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(sK1))
% 43.74/5.99      | X0 != k1_xboole_0
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X1,X1,X1,X1)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1408]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_28942,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_3064]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_28945,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_28942]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_11,plain,
% 43.74/5.99      ( r2_hidden(X0,k1_relat_1(X1))
% 43.74/5.99      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
% 43.74/5.99      | ~ v1_relat_1(X1) ),
% 43.74/5.99      inference(cnf_transformation,[],[f47]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1113,plain,
% 43.74/5.99      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK1,X1)))
% 43.74/5.99      | r2_hidden(X0,k1_relat_1(sK1))
% 43.74/5.99      | ~ v1_relat_1(sK1) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_11]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_43632,plain,
% 43.74/5.99      ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | r2_hidden(sK0,k1_relat_1(sK1))
% 43.74/5.99      | ~ v1_relat_1(sK1) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1113]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_7482,plain,
% 43.74/5.99      ( X0 != k1_xboole_0 | k2_relat_1(X0) = k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_329]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_24432,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1))) != k1_xboole_0
% 43.74/5.99      | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(k7_relat_1(sK1,X1)))) = k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_7482]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_58464,plain,
% 43.74/5.99      ( k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) != k1_xboole_0
% 43.74/5.99      | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) = k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_24432]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_66448,plain,
% 43.74/5.99      ( r1_tarski(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_3]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_3243,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | r1_tarski(k7_relat_1(k7_relat_1(sK1,X2),X3),X4)
% 43.74/5.99      | X4 != X1
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,X2),X3) != X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_324]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_7994,plain,
% 43.74/5.99      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),X1)
% 43.74/5.99      | ~ r1_tarski(k1_xboole_0,X2)
% 43.74/5.99      | X1 != X2
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_3243]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_66467,plain,
% 43.74/5.99      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | ~ r1_tarski(k1_xboole_0,X1)
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_7994]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_101458,plain,
% 43.74/5.99      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | ~ r1_tarski(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) != k1_xboole_0
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_66467]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_101460,plain,
% 43.74/5.99      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | ~ r1_tarski(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)) != k1_xboole_0
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_101458]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_1267,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2)
% 43.74/5.99      | X2 != X1
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_324]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_28943,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),X1)
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X2)
% 43.74/5.99      | X2 != X1
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_1267]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_68677,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),X1)
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_28943]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_101680,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)),k1_relat_1(sK1))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_68677]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_101682,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(sK1))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_101680]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_135568,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,X2),X3)
% 43.74/5.99      | X3 != X1
% 43.74/5.99      | k7_relat_1(sK1,X2) != X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_324]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_137643,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1)
% 43.74/5.99      | X1 != X0
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_135568]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_142376,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k1_xboole_0 != X0 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_137643]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_133503,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,X1)
% 43.74/5.99      | r1_tarski(X2,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | X2 != X0
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != X1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_324]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_135561,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | r1_tarski(X1,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | X1 != X0
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_133503]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_142320,plain,
% 43.74/5.99      ( r1_tarski(X0,k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | X0 != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_135561]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_145603,plain,
% 43.74/5.99      ( r1_tarski(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | ~ r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 43.74/5.99      | k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_142320]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_139152,plain,
% 43.74/5.99      ( X0 != X1
% 43.74/5.99      | X0 = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
% 43.74/5.99      | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != X1 ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_323]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_140423,plain,
% 43.74/5.99      ( X0 != k2_relat_1(X1)
% 43.74/5.99      | X0 = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
% 43.74/5.99      | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_relat_1(X1) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_139152]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_157242,plain,
% 43.74/5.99      ( X0 = k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))
% 43.74/5.99      | X0 != k2_relat_1(k1_xboole_0)
% 43.74/5.99      | k2_relat_1(k7_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k1_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) != k2_relat_1(k1_xboole_0) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_140423]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_141123,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X1)
% 43.74/5.99      | X1 != X0
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_135568]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_166412,plain,
% 43.74/5.99      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)),k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
% 43.74/5.99      | r1_tarski(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),X0)
% 43.74/5.99      | X0 != k2_relat_1(k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
% 43.74/5.99      | k7_relat_1(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) != k7_relat_1(k7_relat_1(sK1,k1_relat_1(sK1)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 43.74/5.99      inference(instantiation,[status(thm)],[c_141123]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_167105,plain,
% 43.74/5.99      ( X0 != k1_xboole_0 ),
% 43.74/5.99      inference(global_propositional_subsumption,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_158153,c_17,c_15,c_52,c_56,c_211,c_334,c_650,c_773,c_787,
% 43.74/5.99                 c_862,c_863,c_1002,c_1261,c_1262,c_1428,c_1703,c_1704,
% 43.74/5.99                 c_1964,c_2220,c_2483,c_2754,c_3957,c_4703,c_4771,c_6986,
% 43.74/5.99                 c_12295,c_16211,c_16213,c_24541,c_28945,c_43632,c_58464,
% 43.74/5.99                 c_66448,c_101460,c_101682,c_142376,c_145603,c_157242,c_166412]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_167111,plain,
% 43.74/5.99      ( ~ r1_tarski(X0,k1_relat_1(k1_relat_1(k1_xboole_0))) ),
% 43.74/5.99      inference(global_propositional_subsumption,
% 43.74/5.99                [status(thm)],
% 43.74/5.99                [c_158435,c_17,c_15,c_3,c_52,c_56,c_211,c_334,c_650,c_773,
% 43.74/5.99                 c_787,c_862,c_863,c_1002,c_1261,c_1262,c_1428,c_1478,c_1703,
% 43.74/5.99                 c_1704,c_1964,c_2220,c_2483,c_2754,c_3957,c_4703,c_4771,
% 43.74/5.99                 c_6986,c_9646,c_12295,c_16211,c_16213,c_18223,c_24541,
% 43.74/5.99                 c_28945,c_43632,c_58464,c_66448,c_101460,c_101682,c_142376,
% 43.74/5.99                 c_145603,c_157242,c_166412]) ).
% 43.74/5.99  
% 43.74/5.99  cnf(c_167135,plain,
% 43.74/5.99      ( $false ),
% 43.74/5.99      inference(resolution,[status(thm)],[c_167111,c_1]) ).
% 43.74/5.99  
% 43.74/5.99  
% 43.74/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.74/5.99  
% 43.74/5.99  ------                               Statistics
% 43.74/5.99  
% 43.74/5.99  ------ Selected
% 43.74/5.99  
% 43.74/5.99  total_time:                             5.465
% 43.74/5.99  
%------------------------------------------------------------------------------
