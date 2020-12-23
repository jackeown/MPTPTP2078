%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:10 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 437 expanded)
%              Number of clauses        :   65 ( 102 expanded)
%              Number of leaves         :   21 ( 104 expanded)
%              Depth                    :   22
%              Number of atoms          :  349 (1073 expanded)
%              Number of equality atoms :  191 ( 602 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK2,sK1)) != k2_relat_1(sK2)
      & k1_tarski(sK1) = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_tarski(k1_funct_1(sK2,sK1)) != k2_relat_1(sK2)
    & k1_tarski(sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f39])).

fof(f66,plain,(
    k1_tarski(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f79,plain,(
    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK2) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f54,f71])).

fof(f64,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f71])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    k1_tarski(k1_funct_1(sK2,sK1)) != k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    k4_enumset1(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1)) != k2_relat_1(sK2) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f55,f71])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_617,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_19,negated_conjecture,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7,plain,
    ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
    | r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_614,plain,
    ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) != iProver_top
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1123,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | r2_hidden(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_614])).

cnf(c_1261,plain,
    ( r2_hidden(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_1123])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_607,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_609,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2565,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k11_relat_1(X1,X0)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_607,c_609])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_620,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6209,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k11_relat_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_620])).

cnf(c_6413,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k11_relat_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_6209])).

cnf(c_9,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_613,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_603,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_608,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1774,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_608])).

cnf(c_2094,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_603,c_1774])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_611,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_925,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_603,c_611])).

cnf(c_2238,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2094,c_925])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_612,plain,
    ( k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1864,plain,
    ( k9_relat_1(sK2,k4_enumset1(X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_603,c_612])).

cnf(c_1998,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k11_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_19,c_1864])).

cnf(c_2240,plain,
    ( k11_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2238,c_1998])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_610,plain,
    ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2360,plain,
    ( r2_hidden(X0,k2_relat_1(sK2)) != iProver_top
    | r2_hidden(k4_tarski(sK1,X0),sK2) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2240,c_610])).

cnf(c_22,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2524,plain,
    ( r2_hidden(k4_tarski(sK1,X0),sK2) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2360,c_22])).

cnf(c_2525,plain,
    ( r2_hidden(X0,k2_relat_1(sK2)) != iProver_top
    | r2_hidden(k4_tarski(sK1,X0),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2524])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_606,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2535,plain,
    ( k1_funct_1(sK2,sK1) = X0
    | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_606])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3554,plain,
    ( k1_funct_1(sK2,sK1) = X0
    | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2535,c_22,c_23])).

cnf(c_3562,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k2_relat_1(sK2)
    | sK0(k2_relat_1(sK2),X0) = k1_funct_1(sK2,sK1)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_613,c_3554])).

cnf(c_18,negated_conjecture,
    ( k4_enumset1(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1)) != k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3837,plain,
    ( sK0(k2_relat_1(sK2),k1_funct_1(sK2,sK1)) = k1_funct_1(sK2,sK1)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3562,c_18])).

cnf(c_8,plain,
    ( k4_enumset1(X0,X0,X0,X0,X0,X0) = X1
    | sK0(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_899,plain,
    ( k4_enumset1(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1)) = k2_relat_1(sK2)
    | sK0(k2_relat_1(sK2),k1_funct_1(sK2,sK1)) != k1_funct_1(sK2,sK1)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_281,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_965,plain,
    ( k2_relat_1(sK2) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1110,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_273,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1111,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_274,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_963,plain,
    ( X0 != X1
    | k2_relat_1(sK2) != X1
    | k2_relat_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_1196,plain,
    ( X0 != k2_relat_1(sK2)
    | k2_relat_1(sK2) = X0
    | k2_relat_1(sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_1694,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_4205,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3837,c_18,c_899,c_1110,c_1111,c_1694])).

cnf(c_4214,plain,
    ( k11_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4205,c_2240])).

cnf(c_6425,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6413,c_4214])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_66,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6425,c_66,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:07:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.65/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.98  
% 3.65/0.98  ------  iProver source info
% 3.65/0.98  
% 3.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.98  git: non_committed_changes: false
% 3.65/0.98  git: last_make_outside_of_git: false
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  ------ Parsing...
% 3.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.98  ------ Proving...
% 3.65/0.98  ------ Problem Properties 
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  clauses                                 21
% 3.65/0.98  conjectures                             4
% 3.65/0.98  EPR                                     6
% 3.65/0.98  Horn                                    19
% 3.65/0.98  unary                                   6
% 3.65/0.98  binary                                  5
% 3.65/0.98  lits                                    49
% 3.65/0.98  lits eq                                 12
% 3.65/0.98  fd_pure                                 0
% 3.65/0.98  fd_pseudo                               0
% 3.65/0.98  fd_cond                                 0
% 3.65/0.98  fd_pseudo_cond                          4
% 3.65/0.98  AC symbols                              0
% 3.65/0.98  
% 3.65/0.98  ------ Input Options Time Limit: Unbounded
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  Current options:
% 3.65/0.98  ------ 
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ Proving...
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS status Theorem for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  fof(f3,axiom,(
% 3.65/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f30,plain,(
% 3.65/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.65/0.98    inference(nnf_transformation,[],[f3])).
% 3.65/0.98  
% 3.65/0.98  fof(f31,plain,(
% 3.65/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.65/0.98    inference(flattening,[],[f30])).
% 3.65/0.98  
% 3.65/0.98  fof(f43,plain,(
% 3.65/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.65/0.98    inference(cnf_transformation,[],[f31])).
% 3.65/0.98  
% 3.65/0.98  fof(f81,plain,(
% 3.65/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.65/0.98    inference(equality_resolution,[],[f43])).
% 3.65/0.98  
% 3.65/0.98  fof(f16,conjecture,(
% 3.65/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f17,negated_conjecture,(
% 3.65/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.65/0.98    inference(negated_conjecture,[],[f16])).
% 3.65/0.98  
% 3.65/0.98  fof(f28,plain,(
% 3.65/0.98    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.65/0.98    inference(ennf_transformation,[],[f17])).
% 3.65/0.98  
% 3.65/0.98  fof(f29,plain,(
% 3.65/0.98    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.65/0.98    inference(flattening,[],[f28])).
% 3.65/0.98  
% 3.65/0.98  fof(f39,plain,(
% 3.65/0.98    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK2,sK1)) != k2_relat_1(sK2) & k1_tarski(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f40,plain,(
% 3.65/0.98    k1_tarski(k1_funct_1(sK2,sK1)) != k2_relat_1(sK2) & k1_tarski(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f39])).
% 3.65/0.98  
% 3.65/0.98  fof(f66,plain,(
% 3.65/0.98    k1_tarski(sK1) = k1_relat_1(sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f40])).
% 3.65/0.98  
% 3.65/0.98  fof(f4,axiom,(
% 3.65/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f46,plain,(
% 3.65/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f4])).
% 3.65/0.98  
% 3.65/0.98  fof(f5,axiom,(
% 3.65/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f47,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f5])).
% 3.65/0.98  
% 3.65/0.98  fof(f6,axiom,(
% 3.65/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f48,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f6])).
% 3.65/0.98  
% 3.65/0.98  fof(f7,axiom,(
% 3.65/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f49,plain,(
% 3.65/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f7])).
% 3.65/0.98  
% 3.65/0.98  fof(f8,axiom,(
% 3.65/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f50,plain,(
% 3.65/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f8])).
% 3.65/0.98  
% 3.65/0.98  fof(f68,plain,(
% 3.65/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.65/0.98    inference(definition_unfolding,[],[f49,f50])).
% 3.65/0.98  
% 3.65/0.98  fof(f69,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.65/0.98    inference(definition_unfolding,[],[f48,f68])).
% 3.65/0.98  
% 3.65/0.98  fof(f70,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.65/0.98    inference(definition_unfolding,[],[f47,f69])).
% 3.65/0.98  
% 3.65/0.98  fof(f71,plain,(
% 3.65/0.98    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 3.65/0.98    inference(definition_unfolding,[],[f46,f70])).
% 3.65/0.98  
% 3.65/0.98  fof(f79,plain,(
% 3.65/0.98    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK2)),
% 3.65/0.98    inference(definition_unfolding,[],[f66,f71])).
% 3.65/0.98  
% 3.65/0.98  fof(f9,axiom,(
% 3.65/0.98    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f32,plain,(
% 3.65/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.65/0.98    inference(nnf_transformation,[],[f9])).
% 3.65/0.98  
% 3.65/0.98  fof(f33,plain,(
% 3.65/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.65/0.98    inference(flattening,[],[f32])).
% 3.65/0.98  
% 3.65/0.98  fof(f51,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f33])).
% 3.65/0.98  
% 3.65/0.98  fof(f74,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)) )),
% 3.65/0.98    inference(definition_unfolding,[],[f51,f70])).
% 3.65/0.98  
% 3.65/0.98  fof(f15,axiom,(
% 3.65/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f26,plain,(
% 3.65/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.65/0.98    inference(ennf_transformation,[],[f15])).
% 3.65/0.98  
% 3.65/0.98  fof(f27,plain,(
% 3.65/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.65/0.98    inference(flattening,[],[f26])).
% 3.65/0.98  
% 3.65/0.98  fof(f37,plain,(
% 3.65/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.65/0.98    inference(nnf_transformation,[],[f27])).
% 3.65/0.98  
% 3.65/0.98  fof(f38,plain,(
% 3.65/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.65/0.98    inference(flattening,[],[f37])).
% 3.65/0.98  
% 3.65/0.98  fof(f63,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f38])).
% 3.65/0.98  
% 3.65/0.98  fof(f82,plain,(
% 3.65/0.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.65/0.98    inference(equality_resolution,[],[f63])).
% 3.65/0.98  
% 3.65/0.98  fof(f13,axiom,(
% 3.65/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f23,plain,(
% 3.65/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 3.65/0.98    inference(ennf_transformation,[],[f13])).
% 3.65/0.98  
% 3.65/0.98  fof(f36,plain,(
% 3.65/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 3.65/0.98    inference(nnf_transformation,[],[f23])).
% 3.65/0.98  
% 3.65/0.98  fof(f58,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f36])).
% 3.65/0.98  
% 3.65/0.98  fof(f1,axiom,(
% 3.65/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f18,plain,(
% 3.65/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.65/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 3.65/0.98  
% 3.65/0.98  fof(f19,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f18])).
% 3.65/0.98  
% 3.65/0.98  fof(f41,plain,(
% 3.65/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f19])).
% 3.65/0.98  
% 3.65/0.98  fof(f10,axiom,(
% 3.65/0.98    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f20,plain,(
% 3.65/0.98    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.65/0.98    inference(ennf_transformation,[],[f10])).
% 3.65/0.98  
% 3.65/0.98  fof(f34,plain,(
% 3.65/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f35,plain,(
% 3.65/0.98    ! [X0,X1] : ((sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f34])).
% 3.65/0.98  
% 3.65/0.98  fof(f54,plain,(
% 3.65/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.65/0.98    inference(cnf_transformation,[],[f35])).
% 3.65/0.98  
% 3.65/0.98  fof(f76,plain,(
% 3.65/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 3.65/0.98    inference(definition_unfolding,[],[f54,f71])).
% 3.65/0.98  
% 3.65/0.98  fof(f64,plain,(
% 3.65/0.98    v1_relat_1(sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f40])).
% 3.65/0.98  
% 3.65/0.98  fof(f14,axiom,(
% 3.65/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f24,plain,(
% 3.65/0.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.65/0.98    inference(ennf_transformation,[],[f14])).
% 3.65/0.98  
% 3.65/0.98  fof(f25,plain,(
% 3.65/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.65/0.98    inference(flattening,[],[f24])).
% 3.65/0.98  
% 3.65/0.98  fof(f60,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f25])).
% 3.65/0.98  
% 3.65/0.98  fof(f12,axiom,(
% 3.65/0.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f22,plain,(
% 3.65/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.65/0.98    inference(ennf_transformation,[],[f12])).
% 3.65/0.98  
% 3.65/0.98  fof(f57,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f22])).
% 3.65/0.98  
% 3.65/0.98  fof(f11,axiom,(
% 3.65/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f21,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f11])).
% 3.65/0.98  
% 3.65/0.98  fof(f56,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f21])).
% 3.65/0.98  
% 3.65/0.98  fof(f77,plain,(
% 3.65/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.65/0.98    inference(definition_unfolding,[],[f56,f71])).
% 3.65/0.98  
% 3.65/0.98  fof(f59,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f36])).
% 3.65/0.98  
% 3.65/0.98  fof(f62,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f38])).
% 3.65/0.98  
% 3.65/0.98  fof(f65,plain,(
% 3.65/0.98    v1_funct_1(sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f40])).
% 3.65/0.98  
% 3.65/0.98  fof(f67,plain,(
% 3.65/0.98    k1_tarski(k1_funct_1(sK2,sK1)) != k2_relat_1(sK2)),
% 3.65/0.98    inference(cnf_transformation,[],[f40])).
% 3.65/0.98  
% 3.65/0.98  fof(f78,plain,(
% 3.65/0.98    k4_enumset1(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1)) != k2_relat_1(sK2)),
% 3.65/0.98    inference(definition_unfolding,[],[f67,f71])).
% 3.65/0.98  
% 3.65/0.98  fof(f55,plain,(
% 3.65/0.98    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.65/0.98    inference(cnf_transformation,[],[f35])).
% 3.65/0.98  
% 3.65/0.98  fof(f75,plain,(
% 3.65/0.98    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 3.65/0.98    inference(definition_unfolding,[],[f55,f71])).
% 3.65/0.98  
% 3.65/0.98  fof(f2,axiom,(
% 3.65/0.98    v1_xboole_0(k1_xboole_0)),
% 3.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f42,plain,(
% 3.65/0.98    v1_xboole_0(k1_xboole_0)),
% 3.65/0.98    inference(cnf_transformation,[],[f2])).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4,plain,
% 3.65/0.98      ( r1_tarski(X0,X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_617,plain,
% 3.65/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_19,negated_conjecture,
% 3.65/0.98      ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k1_relat_1(sK2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_7,plain,
% 3.65/0.98      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
% 3.65/0.98      | r2_hidden(X0,X2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_614,plain,
% 3.65/0.98      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) != iProver_top
% 3.65/0.98      | r2_hidden(X0,X2) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1123,plain,
% 3.65/0.98      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 3.65/0.98      | r2_hidden(sK1,X0) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_19,c_614]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1261,plain,
% 3.65/0.98      ( r2_hidden(sK1,k1_relat_1(sK2)) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_617,c_1123]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_15,plain,
% 3.65/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.65/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.65/0.98      | ~ v1_funct_1(X1)
% 3.65/0.98      | ~ v1_relat_1(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_607,plain,
% 3.65/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.65/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1) = iProver_top
% 3.65/0.98      | v1_funct_1(X1) != iProver_top
% 3.65/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13,plain,
% 3.65/0.98      ( r2_hidden(X0,k11_relat_1(X1,X2))
% 3.65/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.65/0.98      | ~ v1_relat_1(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_609,plain,
% 3.65/0.98      ( r2_hidden(X0,k11_relat_1(X1,X2)) = iProver_top
% 3.65/0.98      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 3.65/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2565,plain,
% 3.65/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.65/0.98      | r2_hidden(k1_funct_1(X1,X0),k11_relat_1(X1,X0)) = iProver_top
% 3.65/0.98      | v1_funct_1(X1) != iProver_top
% 3.65/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_607,c_609]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_0,plain,
% 3.65/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_620,plain,
% 3.65/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.65/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6209,plain,
% 3.65/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.65/0.98      | v1_funct_1(X1) != iProver_top
% 3.65/0.98      | v1_relat_1(X1) != iProver_top
% 3.65/0.98      | v1_xboole_0(k11_relat_1(X1,X0)) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2565,c_620]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6413,plain,
% 3.65/0.98      ( v1_funct_1(sK2) != iProver_top
% 3.65/0.98      | v1_relat_1(sK2) != iProver_top
% 3.65/0.98      | v1_xboole_0(k11_relat_1(sK2,sK1)) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_1261,c_6209]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9,plain,
% 3.65/0.98      ( r2_hidden(sK0(X0,X1),X0)
% 3.65/0.98      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
% 3.65/0.98      | k1_xboole_0 = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_613,plain,
% 3.65/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = X1
% 3.65/0.98      | k1_xboole_0 = X1
% 3.65/0.98      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_21,negated_conjecture,
% 3.65/0.98      ( v1_relat_1(sK2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_603,plain,
% 3.65/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_14,plain,
% 3.65/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.65/0.98      | ~ v1_relat_1(X0)
% 3.65/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_608,plain,
% 3.65/0.98      ( k7_relat_1(X0,X1) = X0
% 3.65/0.98      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.65/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1774,plain,
% 3.65/0.98      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.65/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_617,c_608]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2094,plain,
% 3.65/0.98      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_603,c_1774]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11,plain,
% 3.65/0.98      ( ~ v1_relat_1(X0)
% 3.65/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_611,plain,
% 3.65/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.65/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_925,plain,
% 3.65/0.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_603,c_611]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2238,plain,
% 3.65/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2094,c_925]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_10,plain,
% 3.65/0.98      ( ~ v1_relat_1(X0)
% 3.65/0.98      | k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_612,plain,
% 3.65/0.98      ( k9_relat_1(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.65/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1864,plain,
% 3.65/0.98      ( k9_relat_1(sK2,k4_enumset1(X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK2,X0) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_603,c_612]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1998,plain,
% 3.65/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k11_relat_1(sK2,sK1) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_19,c_1864]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2240,plain,
% 3.65/0.98      ( k11_relat_1(sK2,sK1) = k2_relat_1(sK2) ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_2238,c_1998]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12,plain,
% 3.65/0.98      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 3.65/0.98      | r2_hidden(k4_tarski(X2,X0),X1)
% 3.65/0.98      | ~ v1_relat_1(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_610,plain,
% 3.65/0.98      ( r2_hidden(X0,k11_relat_1(X1,X2)) != iProver_top
% 3.65/0.98      | r2_hidden(k4_tarski(X2,X0),X1) = iProver_top
% 3.65/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2360,plain,
% 3.65/0.98      ( r2_hidden(X0,k2_relat_1(sK2)) != iProver_top
% 3.65/0.98      | r2_hidden(k4_tarski(sK1,X0),sK2) = iProver_top
% 3.65/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2240,c_610]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_22,plain,
% 3.65/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2524,plain,
% 3.65/0.98      ( r2_hidden(k4_tarski(sK1,X0),sK2) = iProver_top
% 3.65/0.98      | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_2360,c_22]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2525,plain,
% 3.65/0.98      ( r2_hidden(X0,k2_relat_1(sK2)) != iProver_top
% 3.65/0.98      | r2_hidden(k4_tarski(sK1,X0),sK2) = iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_2524]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_16,plain,
% 3.65/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.65/0.98      | ~ v1_funct_1(X2)
% 3.65/0.98      | ~ v1_relat_1(X2)
% 3.65/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.65/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_606,plain,
% 3.65/0.98      ( k1_funct_1(X0,X1) = X2
% 3.65/0.98      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.65/0.98      | v1_funct_1(X0) != iProver_top
% 3.65/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_2535,plain,
% 3.65/0.98      ( k1_funct_1(sK2,sK1) = X0
% 3.65/0.98      | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top
% 3.65/0.98      | v1_funct_1(sK2) != iProver_top
% 3.65/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_2525,c_606]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_20,negated_conjecture,
% 3.65/0.98      ( v1_funct_1(sK2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_23,plain,
% 3.65/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3554,plain,
% 3.65/0.98      ( k1_funct_1(sK2,sK1) = X0
% 3.65/0.98      | r2_hidden(X0,k2_relat_1(sK2)) != iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_2535,c_22,c_23]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3562,plain,
% 3.65/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = k2_relat_1(sK2)
% 3.65/0.98      | sK0(k2_relat_1(sK2),X0) = k1_funct_1(sK2,sK1)
% 3.65/0.98      | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_613,c_3554]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_18,negated_conjecture,
% 3.65/0.98      ( k4_enumset1(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1)) != k2_relat_1(sK2) ),
% 3.65/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3837,plain,
% 3.65/0.98      ( sK0(k2_relat_1(sK2),k1_funct_1(sK2,sK1)) = k1_funct_1(sK2,sK1)
% 3.65/0.98      | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3562,c_18]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8,plain,
% 3.65/0.98      ( k4_enumset1(X0,X0,X0,X0,X0,X0) = X1
% 3.65/0.98      | sK0(X1,X0) != X0
% 3.65/0.98      | k1_xboole_0 = X1 ),
% 3.65/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_899,plain,
% 3.65/0.98      ( k4_enumset1(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK1)) = k2_relat_1(sK2)
% 3.65/0.98      | sK0(k2_relat_1(sK2),k1_funct_1(sK2,sK1)) != k1_funct_1(sK2,sK1)
% 3.65/0.98      | k1_xboole_0 = k2_relat_1(sK2) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_281,plain,
% 3.65/0.98      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.65/0.98      theory(equality) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_965,plain,
% 3.65/0.98      ( k2_relat_1(sK2) = k2_relat_1(X0) | sK2 != X0 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_281]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1110,plain,
% 3.65/0.98      ( k2_relat_1(sK2) = k2_relat_1(sK2) | sK2 != sK2 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_965]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_273,plain,( X0 = X0 ),theory(equality) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1111,plain,
% 3.65/0.98      ( sK2 = sK2 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_273]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_274,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_963,plain,
% 3.65/0.98      ( X0 != X1 | k2_relat_1(sK2) != X1 | k2_relat_1(sK2) = X0 ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_274]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1196,plain,
% 3.65/0.98      ( X0 != k2_relat_1(sK2)
% 3.65/0.98      | k2_relat_1(sK2) = X0
% 3.65/0.98      | k2_relat_1(sK2) != k2_relat_1(sK2) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_963]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1694,plain,
% 3.65/0.98      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 3.65/0.98      | k2_relat_1(sK2) = k1_xboole_0
% 3.65/0.98      | k1_xboole_0 != k2_relat_1(sK2) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_1196]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4205,plain,
% 3.65/0.98      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_3837,c_18,c_899,c_1110,c_1111,c_1694]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4214,plain,
% 3.65/0.98      ( k11_relat_1(sK2,sK1) = k1_xboole_0 ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_4205,c_2240]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6425,plain,
% 3.65/0.98      ( v1_funct_1(sK2) != iProver_top
% 3.65/0.98      | v1_relat_1(sK2) != iProver_top
% 3.65/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_6413,c_4214]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_1,plain,
% 3.65/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_66,plain,
% 3.65/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(contradiction,plain,
% 3.65/0.98      ( $false ),
% 3.65/0.98      inference(minisat,[status(thm)],[c_6425,c_66,c_23,c_22]) ).
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  ------                               Statistics
% 3.65/0.98  
% 3.65/0.98  ------ Selected
% 3.65/0.98  
% 3.65/0.98  total_time:                             0.217
% 3.65/0.98  
%------------------------------------------------------------------------------
