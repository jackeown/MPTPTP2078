%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:44 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 446 expanded)
%              Number of clauses        :   89 ( 157 expanded)
%              Number of leaves         :   21 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          :  391 (1155 expanded)
%              Number of equality atoms :  185 ( 378 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k9_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k9_relat_1(X1,X0) != k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(sK2))),k1_tarski(k1_funct_1(sK3,sK2)))
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(sK2))),k1_tarski(k1_funct_1(sK3,sK2)))
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f39])).

fof(f65,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(sK2))),k1_tarski(k1_funct_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f72,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
    inference(definition_unfolding,[],[f67,f69,f69])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k11_relat_1(X1,X0) = k1_xboole_0 )
        & ( k11_relat_1(X1,X0) != k1_xboole_0
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_696,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_702,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_701,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3150,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_701])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_687,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_694,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1197,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_687,c_694])).

cnf(c_16,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1202,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1197,c_16,c_17])).

cnf(c_13,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_691,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2313,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_691])).

cnf(c_2317,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2313,c_17])).

cnf(c_30,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2771,plain,
    ( r1_xboole_0(X0,X0) = iProver_top
    | k1_xboole_0 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2317,c_30])).

cnf(c_2772,plain,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2771])).

cnf(c_2779,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2772])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_700,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3358,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2779,c_700])).

cnf(c_5761,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3150,c_3358])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_900,plain,
    ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_901,plain,
    ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_908,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1092,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_313,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1008,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))))
    | X0 != sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2)))
    | X1 != k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_1382,plain,
    ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0)
    | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))))
    | X0 != k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
    | sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_1384,plain,
    ( X0 != k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
    | sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2)))
    | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_310,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1383,plain,
    ( sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) = sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_1722,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0)
    | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1723,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1722])).

cnf(c_1728,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0)
    | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1729,plain,
    ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0) != iProver_top
    | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_683,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_695,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1801,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_683,c_695])).

cnf(c_2312,plain,
    ( k11_relat_1(sK3,X0) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_691])).

cnf(c_2335,plain,
    ( k11_relat_1(sK3,sK2) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1236,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3049,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK3),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ v1_relat_1(sK3)
    | k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_3051,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK3),k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3049])).

cnf(c_3122,plain,
    ( r1_tarski(k11_relat_1(sK3,sK2),k11_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3127,plain,
    ( r1_tarski(k11_relat_1(sK3,sK2),k11_relat_1(sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3122])).

cnf(c_3569,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_702,c_3358])).

cnf(c_311,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2075,plain,
    ( X0 != X1
    | X0 = k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
    | k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) != X1 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_5270,plain,
    ( X0 != k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | X0 = k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
    | k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) != k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(c_2178,plain,
    ( X0 != X1
    | X0 = k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_7079,plain,
    ( X0 = k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | X0 != k1_xboole_0
    | k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2178])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_698,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3152,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_701])).

cnf(c_7806,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3152,c_3358])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_684,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_690,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_686,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2277,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
    | k11_relat_1(X0,X1) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_686])).

cnf(c_11995,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k11_relat_1(sK3,X0) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_2277])).

cnf(c_12312,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11995,c_24])).

cnf(c_12313,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_12312])).

cnf(c_693,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1590,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_683,c_693])).

cnf(c_685,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1598,plain,
    ( r1_tarski(k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1590,c_685])).

cnf(c_1904,plain,
    ( r1_tarski(k11_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1801,c_1598])).

cnf(c_12419,plain,
    ( k11_relat_1(sK3,sK2) = k1_xboole_0
    | r1_tarski(k11_relat_1(sK3,sK2),k11_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12313,c_1904])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19007,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_19008,plain,
    ( X0 = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19007])).

cnf(c_25094,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5761,c_23,c_24,c_26,c_901,c_1092,c_1384,c_1383,c_1723,c_1729,c_2335,c_3051,c_3127,c_3569,c_5270,c_7079,c_7806,c_12419,c_19008])).

cnf(c_25103,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_696,c_25094])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.87/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/1.50  
% 7.87/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.87/1.50  
% 7.87/1.50  ------  iProver source info
% 7.87/1.50  
% 7.87/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.87/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.87/1.50  git: non_committed_changes: false
% 7.87/1.50  git: last_make_outside_of_git: false
% 7.87/1.50  
% 7.87/1.50  ------ 
% 7.87/1.50  ------ Parsing...
% 7.87/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.50  
% 7.87/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.87/1.50  
% 7.87/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.50  
% 7.87/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.87/1.50  ------ Proving...
% 7.87/1.50  ------ Problem Properties 
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  clauses                                 23
% 7.87/1.50  conjectures                             3
% 7.87/1.50  EPR                                     6
% 7.87/1.50  Horn                                    19
% 7.87/1.50  unary                                   8
% 7.87/1.50  binary                                  7
% 7.87/1.50  lits                                    47
% 7.87/1.50  lits eq                                 11
% 7.87/1.50  fd_pure                                 0
% 7.87/1.50  fd_pseudo                               0
% 7.87/1.50  fd_cond                                 0
% 7.87/1.50  fd_pseudo_cond                          1
% 7.87/1.50  AC symbols                              0
% 7.87/1.50  
% 7.87/1.50  ------ Input Options Time Limit: Unbounded
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  ------ 
% 7.87/1.50  Current options:
% 7.87/1.50  ------ 
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  ------ Proving...
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  % SZS status Theorem for theBenchmark.p
% 7.87/1.50  
% 7.87/1.50   Resolution empty clause
% 7.87/1.50  
% 7.87/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.50  
% 7.87/1.50  fof(f3,axiom,(
% 7.87/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f35,plain,(
% 7.87/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.87/1.50    inference(nnf_transformation,[],[f3])).
% 7.87/1.50  
% 7.87/1.50  fof(f36,plain,(
% 7.87/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.87/1.50    inference(flattening,[],[f35])).
% 7.87/1.50  
% 7.87/1.50  fof(f48,plain,(
% 7.87/1.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.87/1.50    inference(cnf_transformation,[],[f36])).
% 7.87/1.50  
% 7.87/1.50  fof(f73,plain,(
% 7.87/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.87/1.50    inference(equality_resolution,[],[f48])).
% 7.87/1.50  
% 7.87/1.50  fof(f1,axiom,(
% 7.87/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f18,plain,(
% 7.87/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.87/1.50    inference(ennf_transformation,[],[f1])).
% 7.87/1.50  
% 7.87/1.50  fof(f29,plain,(
% 7.87/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.87/1.50    inference(nnf_transformation,[],[f18])).
% 7.87/1.50  
% 7.87/1.50  fof(f30,plain,(
% 7.87/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.87/1.50    inference(rectify,[],[f29])).
% 7.87/1.50  
% 7.87/1.50  fof(f31,plain,(
% 7.87/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.87/1.50    introduced(choice_axiom,[])).
% 7.87/1.50  
% 7.87/1.50  fof(f32,plain,(
% 7.87/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.87/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.87/1.50  
% 7.87/1.50  fof(f42,plain,(
% 7.87/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f32])).
% 7.87/1.50  
% 7.87/1.50  fof(f41,plain,(
% 7.87/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f32])).
% 7.87/1.50  
% 7.87/1.50  fof(f13,axiom,(
% 7.87/1.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f62,plain,(
% 7.87/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.87/1.50    inference(cnf_transformation,[],[f13])).
% 7.87/1.50  
% 7.87/1.50  fof(f8,axiom,(
% 7.87/1.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f21,plain,(
% 7.87/1.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.87/1.50    inference(ennf_transformation,[],[f8])).
% 7.87/1.50  
% 7.87/1.50  fof(f54,plain,(
% 7.87/1.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f21])).
% 7.87/1.50  
% 7.87/1.50  fof(f12,axiom,(
% 7.87/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f61,plain,(
% 7.87/1.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.87/1.50    inference(cnf_transformation,[],[f12])).
% 7.87/1.50  
% 7.87/1.50  fof(f60,plain,(
% 7.87/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.87/1.50    inference(cnf_transformation,[],[f12])).
% 7.87/1.50  
% 7.87/1.50  fof(f10,axiom,(
% 7.87/1.50    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f23,plain,(
% 7.87/1.50    ! [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.87/1.50    inference(ennf_transformation,[],[f10])).
% 7.87/1.50  
% 7.87/1.50  fof(f37,plain,(
% 7.87/1.50    ! [X0,X1] : (((k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 7.87/1.50    inference(nnf_transformation,[],[f23])).
% 7.87/1.50  
% 7.87/1.50  fof(f56,plain,(
% 7.87/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f37])).
% 7.87/1.50  
% 7.87/1.50  fof(f2,axiom,(
% 7.87/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f17,plain,(
% 7.87/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.87/1.50    inference(rectify,[],[f2])).
% 7.87/1.50  
% 7.87/1.50  fof(f19,plain,(
% 7.87/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.87/1.50    inference(ennf_transformation,[],[f17])).
% 7.87/1.50  
% 7.87/1.50  fof(f33,plain,(
% 7.87/1.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.87/1.50    introduced(choice_axiom,[])).
% 7.87/1.50  
% 7.87/1.50  fof(f34,plain,(
% 7.87/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.87/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f33])).
% 7.87/1.50  
% 7.87/1.50  fof(f46,plain,(
% 7.87/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f34])).
% 7.87/1.50  
% 7.87/1.50  fof(f15,conjecture,(
% 7.87/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f16,negated_conjecture,(
% 7.87/1.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 7.87/1.50    inference(negated_conjecture,[],[f15])).
% 7.87/1.50  
% 7.87/1.50  fof(f27,plain,(
% 7.87/1.50    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.87/1.50    inference(ennf_transformation,[],[f16])).
% 7.87/1.50  
% 7.87/1.50  fof(f28,plain,(
% 7.87/1.50    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.87/1.50    inference(flattening,[],[f27])).
% 7.87/1.50  
% 7.87/1.50  fof(f39,plain,(
% 7.87/1.50    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(sK2))),k1_tarski(k1_funct_1(sK3,sK2))) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 7.87/1.50    introduced(choice_axiom,[])).
% 7.87/1.50  
% 7.87/1.50  fof(f40,plain,(
% 7.87/1.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(sK2))),k1_tarski(k1_funct_1(sK3,sK2))) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 7.87/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f39])).
% 7.87/1.50  
% 7.87/1.50  fof(f65,plain,(
% 7.87/1.50    v1_relat_1(sK3)),
% 7.87/1.50    inference(cnf_transformation,[],[f40])).
% 7.87/1.50  
% 7.87/1.50  fof(f67,plain,(
% 7.87/1.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_tarski(sK2))),k1_tarski(k1_funct_1(sK3,sK2)))),
% 7.87/1.50    inference(cnf_transformation,[],[f40])).
% 7.87/1.50  
% 7.87/1.50  fof(f4,axiom,(
% 7.87/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f50,plain,(
% 7.87/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f4])).
% 7.87/1.50  
% 7.87/1.50  fof(f5,axiom,(
% 7.87/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f51,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f5])).
% 7.87/1.50  
% 7.87/1.50  fof(f6,axiom,(
% 7.87/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f52,plain,(
% 7.87/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f6])).
% 7.87/1.50  
% 7.87/1.50  fof(f68,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.87/1.50    inference(definition_unfolding,[],[f51,f52])).
% 7.87/1.50  
% 7.87/1.50  fof(f69,plain,(
% 7.87/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.87/1.50    inference(definition_unfolding,[],[f50,f68])).
% 7.87/1.50  
% 7.87/1.50  fof(f72,plain,(
% 7.87/1.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2)))),
% 7.87/1.50    inference(definition_unfolding,[],[f67,f69,f69])).
% 7.87/1.50  
% 7.87/1.50  fof(f9,axiom,(
% 7.87/1.50    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f22,plain,(
% 7.87/1.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.87/1.50    inference(ennf_transformation,[],[f9])).
% 7.87/1.50  
% 7.87/1.50  fof(f55,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f22])).
% 7.87/1.50  
% 7.87/1.50  fof(f7,axiom,(
% 7.87/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f20,plain,(
% 7.87/1.50    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 7.87/1.50    inference(ennf_transformation,[],[f7])).
% 7.87/1.50  
% 7.87/1.50  fof(f53,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f20])).
% 7.87/1.50  
% 7.87/1.50  fof(f70,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 7.87/1.50    inference(definition_unfolding,[],[f53,f69])).
% 7.87/1.50  
% 7.87/1.50  fof(f57,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f37])).
% 7.87/1.50  
% 7.87/1.50  fof(f44,plain,(
% 7.87/1.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f34])).
% 7.87/1.50  
% 7.87/1.50  fof(f66,plain,(
% 7.87/1.50    v1_funct_1(sK3)),
% 7.87/1.50    inference(cnf_transformation,[],[f40])).
% 7.87/1.50  
% 7.87/1.50  fof(f11,axiom,(
% 7.87/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k11_relat_1(X1,X0) != k1_xboole_0))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f24,plain,(
% 7.87/1.50    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k11_relat_1(X1,X0) != k1_xboole_0) | ~v1_relat_1(X1))),
% 7.87/1.50    inference(ennf_transformation,[],[f11])).
% 7.87/1.50  
% 7.87/1.50  fof(f38,plain,(
% 7.87/1.50    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_xboole_0) & (k11_relat_1(X1,X0) != k1_xboole_0 | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 7.87/1.50    inference(nnf_transformation,[],[f24])).
% 7.87/1.50  
% 7.87/1.50  fof(f59,plain,(
% 7.87/1.50    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f38])).
% 7.87/1.50  
% 7.87/1.50  fof(f14,axiom,(
% 7.87/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 7.87/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.50  
% 7.87/1.50  fof(f25,plain,(
% 7.87/1.50    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.87/1.50    inference(ennf_transformation,[],[f14])).
% 7.87/1.50  
% 7.87/1.50  fof(f26,plain,(
% 7.87/1.50    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.87/1.50    inference(flattening,[],[f25])).
% 7.87/1.50  
% 7.87/1.50  fof(f64,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f26])).
% 7.87/1.50  
% 7.87/1.50  fof(f71,plain,(
% 7.87/1.50    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.87/1.50    inference(definition_unfolding,[],[f64,f69])).
% 7.87/1.50  
% 7.87/1.50  fof(f49,plain,(
% 7.87/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.87/1.50    inference(cnf_transformation,[],[f36])).
% 7.87/1.50  
% 7.87/1.50  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f73]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_696,plain,
% 7.87/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1,plain,
% 7.87/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_702,plain,
% 7.87/1.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.87/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2,plain,
% 7.87/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.87/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_701,plain,
% 7.87/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.87/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.87/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3150,plain,
% 7.87/1.50      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 7.87/1.50      | r1_tarski(X0,X2) != iProver_top
% 7.87/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_702,c_701]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_19,plain,
% 7.87/1.50      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.87/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_687,plain,
% 7.87/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10,plain,
% 7.87/1.50      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.87/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_694,plain,
% 7.87/1.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1197,plain,
% 7.87/1.50      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(X0)) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_687,c_694]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_16,plain,
% 7.87/1.50      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_17,plain,
% 7.87/1.50      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1202,plain,
% 7.87/1.50      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_1197,c_16,c_17]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_13,plain,
% 7.87/1.50      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.87/1.50      | ~ v1_relat_1(X0)
% 7.87/1.50      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_691,plain,
% 7.87/1.50      ( k9_relat_1(X0,X1) != k1_xboole_0
% 7.87/1.50      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2313,plain,
% 7.87/1.50      ( k1_xboole_0 != X0
% 7.87/1.50      | r1_xboole_0(k1_relat_1(k6_relat_1(X0)),X0) = iProver_top
% 7.87/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1202,c_691]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2317,plain,
% 7.87/1.50      ( k1_xboole_0 != X0
% 7.87/1.50      | r1_xboole_0(X0,X0) = iProver_top
% 7.87/1.50      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_2313,c_17]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_30,plain,
% 7.87/1.50      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2771,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X0) = iProver_top | k1_xboole_0 != X0 ),
% 7.87/1.50      inference(global_propositional_subsumption,[status(thm)],[c_2317,c_30]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2772,plain,
% 7.87/1.50      ( k1_xboole_0 != X0 | r1_xboole_0(X0,X0) = iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_2771]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2779,plain,
% 7.87/1.50      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.87/1.50      inference(equality_resolution,[status(thm)],[c_2772]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3,plain,
% 7.87/1.50      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 7.87/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_700,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.87/1.50      | r2_hidden(X2,X1) != iProver_top
% 7.87/1.50      | r2_hidden(X2,X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3358,plain,
% 7.87/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2779,c_700]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5761,plain,
% 7.87/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.87/1.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_3150,c_3358]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_23,negated_conjecture,
% 7.87/1.50      ( v1_relat_1(sK3) ),
% 7.87/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_24,plain,
% 7.87/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_21,negated_conjecture,
% 7.87/1.50      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
% 7.87/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_26,plain,
% 7.87/1.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_900,plain,
% 7.87/1.50      ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))))
% 7.87/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_901,plain,
% 7.87/1.50      ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 7.87/1.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_11,plain,
% 7.87/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_908,plain,
% 7.87/1.50      ( ~ v1_relat_1(sK3)
% 7.87/1.50      | k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1092,plain,
% 7.87/1.50      ( ~ v1_relat_1(sK3)
% 7.87/1.50      | k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) = k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_908]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_313,plain,
% 7.87/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.87/1.50      theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1008,plain,
% 7.87/1.50      ( r2_hidden(X0,X1)
% 7.87/1.50      | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))))
% 7.87/1.50      | X0 != sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2)))
% 7.87/1.50      | X1 != k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_313]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1382,plain,
% 7.87/1.50      ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0)
% 7.87/1.50      | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))))
% 7.87/1.50      | X0 != k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
% 7.87/1.50      | sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1008]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1384,plain,
% 7.87/1.50      ( X0 != k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
% 7.87/1.50      | sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2)))
% 7.87/1.50      | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0) = iProver_top
% 7.87/1.50      | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_310,plain,( X0 = X0 ),theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1383,plain,
% 7.87/1.50      ( sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) = sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_310]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1722,plain,
% 7.87/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.87/1.50      | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0)
% 7.87/1.50      | ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1723,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.87/1.50      | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0) != iProver_top
% 7.87/1.50      | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_1722]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1728,plain,
% 7.87/1.50      ( ~ r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0)
% 7.87/1.50      | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1)
% 7.87/1.50      | ~ r1_tarski(X0,X1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1729,plain,
% 7.87/1.50      ( r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X0) != iProver_top
% 7.87/1.50      | r2_hidden(sK0(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))),X1) = iProver_top
% 7.87/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_683,plain,
% 7.87/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9,plain,
% 7.87/1.50      ( ~ v1_relat_1(X0)
% 7.87/1.50      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_695,plain,
% 7.87/1.50      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1801,plain,
% 7.87/1.50      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_683,c_695]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2312,plain,
% 7.87/1.50      ( k11_relat_1(sK3,X0) != k1_xboole_0
% 7.87/1.50      | r1_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = iProver_top
% 7.87/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1801,c_691]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2335,plain,
% 7.87/1.50      ( k11_relat_1(sK3,sK2) != k1_xboole_0
% 7.87/1.50      | r1_xboole_0(k1_relat_1(sK3),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 7.87/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2312]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_12,plain,
% 7.87/1.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.87/1.50      | ~ v1_relat_1(X0)
% 7.87/1.50      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1236,plain,
% 7.87/1.50      ( ~ r1_xboole_0(k1_relat_1(sK3),X0)
% 7.87/1.50      | ~ v1_relat_1(sK3)
% 7.87/1.50      | k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3049,plain,
% 7.87/1.50      ( ~ r1_xboole_0(k1_relat_1(sK3),k2_enumset1(sK2,sK2,sK2,sK2))
% 7.87/1.50      | ~ v1_relat_1(sK3)
% 7.87/1.50      | k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_1236]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3051,plain,
% 7.87/1.50      ( k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k1_xboole_0
% 7.87/1.50      | r1_xboole_0(k1_relat_1(sK3),k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 7.87/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_3049]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3122,plain,
% 7.87/1.50      ( r1_tarski(k11_relat_1(sK3,sK2),k11_relat_1(sK3,sK2)) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3127,plain,
% 7.87/1.50      ( r1_tarski(k11_relat_1(sK3,sK2),k11_relat_1(sK3,sK2)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_3122]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3569,plain,
% 7.87/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_702,c_3358]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_311,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2075,plain,
% 7.87/1.50      ( X0 != X1
% 7.87/1.50      | X0 = k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
% 7.87/1.50      | k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) != X1 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_311]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5270,plain,
% 7.87/1.50      ( X0 != k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
% 7.87/1.50      | X0 = k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)))
% 7.87/1.50      | k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))) != k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2075]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2178,plain,
% 7.87/1.50      ( X0 != X1
% 7.87/1.50      | X0 = k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
% 7.87/1.50      | k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != X1 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_311]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_7079,plain,
% 7.87/1.50      ( X0 = k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
% 7.87/1.50      | X0 != k1_xboole_0
% 7.87/1.50      | k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) != k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2178]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.87/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_698,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X1) = iProver_top
% 7.87/1.50      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3152,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X1) = iProver_top
% 7.87/1.50      | r2_hidden(sK1(X0,X1),X2) = iProver_top
% 7.87/1.50      | r1_tarski(X0,X2) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_698,c_701]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_7806,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X1) = iProver_top
% 7.87/1.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_3152,c_3358]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22,negated_conjecture,
% 7.87/1.50      ( v1_funct_1(sK3) ),
% 7.87/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_684,plain,
% 7.87/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_14,plain,
% 7.87/1.50      ( r2_hidden(X0,k1_relat_1(X1))
% 7.87/1.50      | ~ v1_relat_1(X1)
% 7.87/1.50      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_690,plain,
% 7.87/1.50      ( k11_relat_1(X0,X1) = k1_xboole_0
% 7.87/1.50      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_20,plain,
% 7.87/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.87/1.50      | ~ v1_funct_1(X1)
% 7.87/1.50      | ~ v1_relat_1(X1)
% 7.87/1.50      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 7.87/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_686,plain,
% 7.87/1.50      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
% 7.87/1.50      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 7.87/1.50      | v1_funct_1(X0) != iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2277,plain,
% 7.87/1.50      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
% 7.87/1.50      | k11_relat_1(X0,X1) = k1_xboole_0
% 7.87/1.50      | v1_funct_1(X0) != iProver_top
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_690,c_686]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_11995,plain,
% 7.87/1.50      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.87/1.50      | k11_relat_1(sK3,X0) = k1_xboole_0
% 7.87/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_684,c_2277]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_12312,plain,
% 7.87/1.50      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 7.87/1.50      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 7.87/1.50      inference(global_propositional_subsumption,[status(thm)],[c_11995,c_24]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_12313,plain,
% 7.87/1.50      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 7.87/1.50      | k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_12312]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_693,plain,
% 7.87/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.87/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1590,plain,
% 7.87/1.50      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_683,c_693]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_685,plain,
% 7.87/1.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2))),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1598,plain,
% 7.87/1.50      ( r1_tarski(k9_relat_1(sK3,k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_1590,c_685]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1904,plain,
% 7.87/1.50      ( r1_tarski(k11_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2),k1_funct_1(sK3,sK2))) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_1801,c_1598]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_12419,plain,
% 7.87/1.50      ( k11_relat_1(sK3,sK2) = k1_xboole_0
% 7.87/1.50      | r1_tarski(k11_relat_1(sK3,sK2),k11_relat_1(sK3,sK2)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_12313,c_1904]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6,plain,
% 7.87/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_19007,plain,
% 7.87/1.50      ( ~ r1_tarski(X0,k1_xboole_0)
% 7.87/1.50      | ~ r1_tarski(k1_xboole_0,X0)
% 7.87/1.50      | X0 = k1_xboole_0 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_19008,plain,
% 7.87/1.50      ( X0 = k1_xboole_0
% 7.87/1.50      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.87/1.50      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_19007]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_25094,plain,
% 7.87/1.50      ( r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_5761,c_23,c_24,c_26,c_901,c_1092,c_1384,c_1383,c_1723,
% 7.87/1.50                 c_1729,c_2335,c_3051,c_3127,c_3569,c_5270,c_7079,c_7806,
% 7.87/1.50                 c_12419,c_19008]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_25103,plain,
% 7.87/1.50      ( $false ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_696,c_25094]) ).
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.50  
% 7.87/1.50  ------                               Statistics
% 7.87/1.50  
% 7.87/1.50  ------ Selected
% 7.87/1.50  
% 7.87/1.50  total_time:                             0.78
% 7.87/1.50  
%------------------------------------------------------------------------------
