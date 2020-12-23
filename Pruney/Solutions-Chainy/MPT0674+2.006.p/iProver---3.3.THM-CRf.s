%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:16 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 183 expanded)
%              Number of clauses        :   48 (  52 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  353 ( 596 expanded)
%              Number of equality atoms :  178 ( 263 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0)
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)
      & r2_hidden(sK3,k1_relat_1(sK4))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)
    & r2_hidden(sK3,k1_relat_1(sK4))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f35])).

fof(f58,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    k1_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f73,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f74,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f73])).

fof(f1,axiom,(
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

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f22])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1166,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_516,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK4)
    | ~ r2_hidden(X0,k11_relat_1(sK4,X1)) ),
    inference(prop_impl,[status(thm)],[c_344])).

cnf(c_517,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(renaming,[status(thm)],[c_516])).

cnf(c_1158,plain,
    ( r2_hidden(X0,k11_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_517])).

cnf(c_2450,plain,
    ( k1_enumset1(X0,X0,X0) = k11_relat_1(sK4,X1)
    | k11_relat_1(sK4,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,sK2(k11_relat_1(sK4,X1),X0)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_1158])).

cnf(c_17,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_238,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_239,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_243,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_22])).

cnf(c_1164,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_5942,plain,
    ( k1_enumset1(X0,X0,X0) = k11_relat_1(sK4,X1)
    | k11_relat_1(sK4,X1) = k1_xboole_0
    | sK2(k11_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X1) ),
    inference(superposition,[status(thm)],[c_2450,c_1164])).

cnf(c_19,negated_conjecture,
    ( k1_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_6503,plain,
    ( k11_relat_1(sK4,X0) != k11_relat_1(sK4,sK3)
    | k11_relat_1(sK4,X0) = k1_xboole_0
    | sK2(k11_relat_1(sK4,X0),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_5942,c_19])).

cnf(c_6877,plain,
    ( k11_relat_1(sK4,sK3) = k1_xboole_0
    | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,sK3) ),
    inference(equality_resolution,[status(thm)],[c_6503])).

cnf(c_9,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1387,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k11_relat_1(sK4,sK3)
    | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k1_funct_1(sK4,sK3)
    | k1_xboole_0 = k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_703,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1971,plain,
    ( k11_relat_1(sK4,sK3) = k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_704,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1485,plain,
    ( X0 != X1
    | k11_relat_1(sK4,sK3) != X1
    | k11_relat_1(sK4,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1970,plain,
    ( X0 != k11_relat_1(sK4,sK3)
    | k11_relat_1(sK4,sK3) = X0
    | k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_3490,plain,
    ( k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3)
    | k11_relat_1(sK4,sK3) = k1_xboole_0
    | k1_xboole_0 != k11_relat_1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_7072,plain,
    ( k11_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6877,c_19,c_1387,c_1971,c_3490])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_325,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_326,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_13,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_301,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | k9_relat_1(X0,X1) != k1_xboole_0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_302,plain,
    ( r1_xboole_0(k1_relat_1(sK4),X0)
    | k9_relat_1(sK4,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_512,plain,
    ( r1_xboole_0(k1_relat_1(sK4),X0)
    | k9_relat_1(sK4,X0) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_302])).

cnf(c_1161,plain,
    ( k9_relat_1(sK4,X0) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK4),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_1703,plain,
    ( k11_relat_1(sK4,X0) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK4),k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_326,c_1161])).

cnf(c_7144,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7072,c_1703])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1169,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1175,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2120,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,k1_enumset1(X2,X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_1175])).

cnf(c_8831,plain,
    ( r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_2120])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK3,k1_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8831,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.39/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/0.99  
% 3.39/0.99  ------  iProver source info
% 3.39/0.99  
% 3.39/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.39/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/0.99  git: non_committed_changes: false
% 3.39/0.99  git: last_make_outside_of_git: false
% 3.39/0.99  
% 3.39/0.99  ------ 
% 3.39/0.99  
% 3.39/0.99  ------ Input Options
% 3.39/0.99  
% 3.39/0.99  --out_options                           all
% 3.39/0.99  --tptp_safe_out                         true
% 3.39/0.99  --problem_path                          ""
% 3.39/0.99  --include_path                          ""
% 3.39/0.99  --clausifier                            res/vclausify_rel
% 3.39/0.99  --clausifier_options                    --mode clausify
% 3.39/0.99  --stdin                                 false
% 3.39/0.99  --stats_out                             all
% 3.39/0.99  
% 3.39/0.99  ------ General Options
% 3.39/0.99  
% 3.39/0.99  --fof                                   false
% 3.39/0.99  --time_out_real                         305.
% 3.39/0.99  --time_out_virtual                      -1.
% 3.39/0.99  --symbol_type_check                     false
% 3.39/0.99  --clausify_out                          false
% 3.39/0.99  --sig_cnt_out                           false
% 3.39/0.99  --trig_cnt_out                          false
% 3.39/0.99  --trig_cnt_out_tolerance                1.
% 3.39/0.99  --trig_cnt_out_sk_spl                   false
% 3.39/0.99  --abstr_cl_out                          false
% 3.39/0.99  
% 3.39/0.99  ------ Global Options
% 3.39/0.99  
% 3.39/0.99  --schedule                              default
% 3.39/0.99  --add_important_lit                     false
% 3.39/0.99  --prop_solver_per_cl                    1000
% 3.39/0.99  --min_unsat_core                        false
% 3.39/0.99  --soft_assumptions                      false
% 3.39/0.99  --soft_lemma_size                       3
% 3.39/0.99  --prop_impl_unit_size                   0
% 3.39/0.99  --prop_impl_unit                        []
% 3.39/0.99  --share_sel_clauses                     true
% 3.39/0.99  --reset_solvers                         false
% 3.39/0.99  --bc_imp_inh                            [conj_cone]
% 3.39/0.99  --conj_cone_tolerance                   3.
% 3.39/0.99  --extra_neg_conj                        none
% 3.39/0.99  --large_theory_mode                     true
% 3.39/0.99  --prolific_symb_bound                   200
% 3.39/0.99  --lt_threshold                          2000
% 3.39/0.99  --clause_weak_htbl                      true
% 3.39/0.99  --gc_record_bc_elim                     false
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing Options
% 3.39/0.99  
% 3.39/0.99  --preprocessing_flag                    true
% 3.39/0.99  --time_out_prep_mult                    0.1
% 3.39/0.99  --splitting_mode                        input
% 3.39/0.99  --splitting_grd                         true
% 3.39/0.99  --splitting_cvd                         false
% 3.39/0.99  --splitting_cvd_svl                     false
% 3.39/0.99  --splitting_nvd                         32
% 3.39/0.99  --sub_typing                            true
% 3.39/0.99  --prep_gs_sim                           true
% 3.39/0.99  --prep_unflatten                        true
% 3.39/0.99  --prep_res_sim                          true
% 3.39/0.99  --prep_upred                            true
% 3.39/0.99  --prep_sem_filter                       exhaustive
% 3.39/0.99  --prep_sem_filter_out                   false
% 3.39/0.99  --pred_elim                             true
% 3.39/0.99  --res_sim_input                         true
% 3.39/0.99  --eq_ax_congr_red                       true
% 3.39/0.99  --pure_diseq_elim                       true
% 3.39/0.99  --brand_transform                       false
% 3.39/0.99  --non_eq_to_eq                          false
% 3.39/0.99  --prep_def_merge                        true
% 3.39/0.99  --prep_def_merge_prop_impl              false
% 3.39/0.99  --prep_def_merge_mbd                    true
% 3.39/0.99  --prep_def_merge_tr_red                 false
% 3.39/0.99  --prep_def_merge_tr_cl                  false
% 3.39/0.99  --smt_preprocessing                     true
% 3.39/0.99  --smt_ac_axioms                         fast
% 3.39/0.99  --preprocessed_out                      false
% 3.39/0.99  --preprocessed_stats                    false
% 3.39/0.99  
% 3.39/0.99  ------ Abstraction refinement Options
% 3.39/0.99  
% 3.39/0.99  --abstr_ref                             []
% 3.39/0.99  --abstr_ref_prep                        false
% 3.39/0.99  --abstr_ref_until_sat                   false
% 3.39/0.99  --abstr_ref_sig_restrict                funpre
% 3.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.99  --abstr_ref_under                       []
% 3.39/0.99  
% 3.39/0.99  ------ SAT Options
% 3.39/0.99  
% 3.39/0.99  --sat_mode                              false
% 3.39/0.99  --sat_fm_restart_options                ""
% 3.39/0.99  --sat_gr_def                            false
% 3.39/0.99  --sat_epr_types                         true
% 3.39/0.99  --sat_non_cyclic_types                  false
% 3.39/0.99  --sat_finite_models                     false
% 3.39/0.99  --sat_fm_lemmas                         false
% 3.39/0.99  --sat_fm_prep                           false
% 3.39/0.99  --sat_fm_uc_incr                        true
% 3.39/0.99  --sat_out_model                         small
% 3.39/0.99  --sat_out_clauses                       false
% 3.39/0.99  
% 3.39/0.99  ------ QBF Options
% 3.39/0.99  
% 3.39/0.99  --qbf_mode                              false
% 3.39/0.99  --qbf_elim_univ                         false
% 3.39/0.99  --qbf_dom_inst                          none
% 3.39/0.99  --qbf_dom_pre_inst                      false
% 3.39/0.99  --qbf_sk_in                             false
% 3.39/0.99  --qbf_pred_elim                         true
% 3.39/0.99  --qbf_split                             512
% 3.39/0.99  
% 3.39/0.99  ------ BMC1 Options
% 3.39/0.99  
% 3.39/0.99  --bmc1_incremental                      false
% 3.39/0.99  --bmc1_axioms                           reachable_all
% 3.39/0.99  --bmc1_min_bound                        0
% 3.39/0.99  --bmc1_max_bound                        -1
% 3.39/0.99  --bmc1_max_bound_default                -1
% 3.39/0.99  --bmc1_symbol_reachability              true
% 3.39/0.99  --bmc1_property_lemmas                  false
% 3.39/0.99  --bmc1_k_induction                      false
% 3.39/0.99  --bmc1_non_equiv_states                 false
% 3.39/0.99  --bmc1_deadlock                         false
% 3.39/0.99  --bmc1_ucm                              false
% 3.39/0.99  --bmc1_add_unsat_core                   none
% 3.39/0.99  --bmc1_unsat_core_children              false
% 3.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.99  --bmc1_out_stat                         full
% 3.39/0.99  --bmc1_ground_init                      false
% 3.39/0.99  --bmc1_pre_inst_next_state              false
% 3.39/0.99  --bmc1_pre_inst_state                   false
% 3.39/0.99  --bmc1_pre_inst_reach_state             false
% 3.39/0.99  --bmc1_out_unsat_core                   false
% 3.39/0.99  --bmc1_aig_witness_out                  false
% 3.39/0.99  --bmc1_verbose                          false
% 3.39/0.99  --bmc1_dump_clauses_tptp                false
% 3.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.99  --bmc1_dump_file                        -
% 3.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.99  --bmc1_ucm_extend_mode                  1
% 3.39/0.99  --bmc1_ucm_init_mode                    2
% 3.39/0.99  --bmc1_ucm_cone_mode                    none
% 3.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.99  --bmc1_ucm_relax_model                  4
% 3.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.99  --bmc1_ucm_layered_model                none
% 3.39/0.99  --bmc1_ucm_max_lemma_size               10
% 3.39/0.99  
% 3.39/0.99  ------ AIG Options
% 3.39/0.99  
% 3.39/0.99  --aig_mode                              false
% 3.39/0.99  
% 3.39/0.99  ------ Instantiation Options
% 3.39/0.99  
% 3.39/0.99  --instantiation_flag                    true
% 3.39/0.99  --inst_sos_flag                         false
% 3.39/0.99  --inst_sos_phase                        true
% 3.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel_side                     num_symb
% 3.39/0.99  --inst_solver_per_active                1400
% 3.39/0.99  --inst_solver_calls_frac                1.
% 3.39/0.99  --inst_passive_queue_type               priority_queues
% 3.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.99  --inst_passive_queues_freq              [25;2]
% 3.39/0.99  --inst_dismatching                      true
% 3.39/0.99  --inst_eager_unprocessed_to_passive     true
% 3.39/0.99  --inst_prop_sim_given                   true
% 3.39/0.99  --inst_prop_sim_new                     false
% 3.39/0.99  --inst_subs_new                         false
% 3.39/0.99  --inst_eq_res_simp                      false
% 3.39/0.99  --inst_subs_given                       false
% 3.39/0.99  --inst_orphan_elimination               true
% 3.39/0.99  --inst_learning_loop_flag               true
% 3.39/0.99  --inst_learning_start                   3000
% 3.39/0.99  --inst_learning_factor                  2
% 3.39/0.99  --inst_start_prop_sim_after_learn       3
% 3.39/0.99  --inst_sel_renew                        solver
% 3.39/0.99  --inst_lit_activity_flag                true
% 3.39/0.99  --inst_restr_to_given                   false
% 3.39/0.99  --inst_activity_threshold               500
% 3.39/0.99  --inst_out_proof                        true
% 3.39/0.99  
% 3.39/0.99  ------ Resolution Options
% 3.39/0.99  
% 3.39/0.99  --resolution_flag                       true
% 3.39/0.99  --res_lit_sel                           adaptive
% 3.39/0.99  --res_lit_sel_side                      none
% 3.39/0.99  --res_ordering                          kbo
% 3.39/0.99  --res_to_prop_solver                    active
% 3.39/0.99  --res_prop_simpl_new                    false
% 3.39/0.99  --res_prop_simpl_given                  true
% 3.39/0.99  --res_passive_queue_type                priority_queues
% 3.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.99  --res_passive_queues_freq               [15;5]
% 3.39/0.99  --res_forward_subs                      full
% 3.39/0.99  --res_backward_subs                     full
% 3.39/0.99  --res_forward_subs_resolution           true
% 3.39/0.99  --res_backward_subs_resolution          true
% 3.39/0.99  --res_orphan_elimination                true
% 3.39/0.99  --res_time_limit                        2.
% 3.39/0.99  --res_out_proof                         true
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Options
% 3.39/0.99  
% 3.39/0.99  --superposition_flag                    true
% 3.39/0.99  --sup_passive_queue_type                priority_queues
% 3.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.99  --demod_completeness_check              fast
% 3.39/0.99  --demod_use_ground                      true
% 3.39/0.99  --sup_to_prop_solver                    passive
% 3.39/0.99  --sup_prop_simpl_new                    true
% 3.39/0.99  --sup_prop_simpl_given                  true
% 3.39/0.99  --sup_fun_splitting                     false
% 3.39/0.99  --sup_smt_interval                      50000
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Simplification Setup
% 3.39/0.99  
% 3.39/0.99  --sup_indices_passive                   []
% 3.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_full_bw                           [BwDemod]
% 3.39/0.99  --sup_immed_triv                        [TrivRules]
% 3.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_immed_bw_main                     []
% 3.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  
% 3.39/0.99  ------ Combination Options
% 3.39/0.99  
% 3.39/0.99  --comb_res_mult                         3
% 3.39/0.99  --comb_sup_mult                         2
% 3.39/0.99  --comb_inst_mult                        10
% 3.39/0.99  
% 3.39/0.99  ------ Debug Options
% 3.39/0.99  
% 3.39/0.99  --dbg_backtrace                         false
% 3.39/0.99  --dbg_dump_prop_clauses                 false
% 3.39/0.99  --dbg_dump_prop_clauses_file            -
% 3.39/0.99  --dbg_out_stat                          false
% 3.39/0.99  ------ Parsing...
% 3.39/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/0.99  ------ Proving...
% 3.39/0.99  ------ Problem Properties 
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  clauses                                 21
% 3.39/0.99  conjectures                             2
% 3.39/0.99  EPR                                     1
% 3.39/0.99  Horn                                    15
% 3.39/0.99  unary                                   5
% 3.39/0.99  binary                                  9
% 3.39/0.99  lits                                    45
% 3.39/0.99  lits eq                                 19
% 3.39/0.99  fd_pure                                 0
% 3.39/0.99  fd_pseudo                               0
% 3.39/0.99  fd_cond                                 0
% 3.39/0.99  fd_pseudo_cond                          6
% 3.39/0.99  AC symbols                              0
% 3.39/0.99  
% 3.39/0.99  ------ Schedule dynamic 5 is on 
% 3.39/0.99  
% 3.39/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  ------ 
% 3.39/0.99  Current options:
% 3.39/0.99  ------ 
% 3.39/0.99  
% 3.39/0.99  ------ Input Options
% 3.39/0.99  
% 3.39/0.99  --out_options                           all
% 3.39/0.99  --tptp_safe_out                         true
% 3.39/0.99  --problem_path                          ""
% 3.39/0.99  --include_path                          ""
% 3.39/0.99  --clausifier                            res/vclausify_rel
% 3.39/0.99  --clausifier_options                    --mode clausify
% 3.39/0.99  --stdin                                 false
% 3.39/0.99  --stats_out                             all
% 3.39/0.99  
% 3.39/0.99  ------ General Options
% 3.39/0.99  
% 3.39/0.99  --fof                                   false
% 3.39/0.99  --time_out_real                         305.
% 3.39/0.99  --time_out_virtual                      -1.
% 3.39/0.99  --symbol_type_check                     false
% 3.39/0.99  --clausify_out                          false
% 3.39/0.99  --sig_cnt_out                           false
% 3.39/0.99  --trig_cnt_out                          false
% 3.39/0.99  --trig_cnt_out_tolerance                1.
% 3.39/0.99  --trig_cnt_out_sk_spl                   false
% 3.39/0.99  --abstr_cl_out                          false
% 3.39/0.99  
% 3.39/0.99  ------ Global Options
% 3.39/0.99  
% 3.39/0.99  --schedule                              default
% 3.39/0.99  --add_important_lit                     false
% 3.39/0.99  --prop_solver_per_cl                    1000
% 3.39/0.99  --min_unsat_core                        false
% 3.39/0.99  --soft_assumptions                      false
% 3.39/0.99  --soft_lemma_size                       3
% 3.39/0.99  --prop_impl_unit_size                   0
% 3.39/0.99  --prop_impl_unit                        []
% 3.39/0.99  --share_sel_clauses                     true
% 3.39/0.99  --reset_solvers                         false
% 3.39/0.99  --bc_imp_inh                            [conj_cone]
% 3.39/0.99  --conj_cone_tolerance                   3.
% 3.39/0.99  --extra_neg_conj                        none
% 3.39/0.99  --large_theory_mode                     true
% 3.39/0.99  --prolific_symb_bound                   200
% 3.39/0.99  --lt_threshold                          2000
% 3.39/0.99  --clause_weak_htbl                      true
% 3.39/0.99  --gc_record_bc_elim                     false
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing Options
% 3.39/0.99  
% 3.39/0.99  --preprocessing_flag                    true
% 3.39/0.99  --time_out_prep_mult                    0.1
% 3.39/0.99  --splitting_mode                        input
% 3.39/0.99  --splitting_grd                         true
% 3.39/0.99  --splitting_cvd                         false
% 3.39/0.99  --splitting_cvd_svl                     false
% 3.39/0.99  --splitting_nvd                         32
% 3.39/0.99  --sub_typing                            true
% 3.39/0.99  --prep_gs_sim                           true
% 3.39/0.99  --prep_unflatten                        true
% 3.39/0.99  --prep_res_sim                          true
% 3.39/0.99  --prep_upred                            true
% 3.39/0.99  --prep_sem_filter                       exhaustive
% 3.39/0.99  --prep_sem_filter_out                   false
% 3.39/0.99  --pred_elim                             true
% 3.39/0.99  --res_sim_input                         true
% 3.39/0.99  --eq_ax_congr_red                       true
% 3.39/0.99  --pure_diseq_elim                       true
% 3.39/0.99  --brand_transform                       false
% 3.39/0.99  --non_eq_to_eq                          false
% 3.39/0.99  --prep_def_merge                        true
% 3.39/0.99  --prep_def_merge_prop_impl              false
% 3.39/0.99  --prep_def_merge_mbd                    true
% 3.39/0.99  --prep_def_merge_tr_red                 false
% 3.39/0.99  --prep_def_merge_tr_cl                  false
% 3.39/0.99  --smt_preprocessing                     true
% 3.39/0.99  --smt_ac_axioms                         fast
% 3.39/0.99  --preprocessed_out                      false
% 3.39/0.99  --preprocessed_stats                    false
% 3.39/0.99  
% 3.39/0.99  ------ Abstraction refinement Options
% 3.39/0.99  
% 3.39/0.99  --abstr_ref                             []
% 3.39/0.99  --abstr_ref_prep                        false
% 3.39/0.99  --abstr_ref_until_sat                   false
% 3.39/0.99  --abstr_ref_sig_restrict                funpre
% 3.39/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/0.99  --abstr_ref_under                       []
% 3.39/0.99  
% 3.39/0.99  ------ SAT Options
% 3.39/0.99  
% 3.39/0.99  --sat_mode                              false
% 3.39/0.99  --sat_fm_restart_options                ""
% 3.39/0.99  --sat_gr_def                            false
% 3.39/0.99  --sat_epr_types                         true
% 3.39/0.99  --sat_non_cyclic_types                  false
% 3.39/0.99  --sat_finite_models                     false
% 3.39/0.99  --sat_fm_lemmas                         false
% 3.39/0.99  --sat_fm_prep                           false
% 3.39/0.99  --sat_fm_uc_incr                        true
% 3.39/0.99  --sat_out_model                         small
% 3.39/0.99  --sat_out_clauses                       false
% 3.39/0.99  
% 3.39/0.99  ------ QBF Options
% 3.39/0.99  
% 3.39/0.99  --qbf_mode                              false
% 3.39/0.99  --qbf_elim_univ                         false
% 3.39/0.99  --qbf_dom_inst                          none
% 3.39/0.99  --qbf_dom_pre_inst                      false
% 3.39/0.99  --qbf_sk_in                             false
% 3.39/0.99  --qbf_pred_elim                         true
% 3.39/0.99  --qbf_split                             512
% 3.39/0.99  
% 3.39/0.99  ------ BMC1 Options
% 3.39/0.99  
% 3.39/0.99  --bmc1_incremental                      false
% 3.39/0.99  --bmc1_axioms                           reachable_all
% 3.39/0.99  --bmc1_min_bound                        0
% 3.39/0.99  --bmc1_max_bound                        -1
% 3.39/0.99  --bmc1_max_bound_default                -1
% 3.39/0.99  --bmc1_symbol_reachability              true
% 3.39/0.99  --bmc1_property_lemmas                  false
% 3.39/0.99  --bmc1_k_induction                      false
% 3.39/0.99  --bmc1_non_equiv_states                 false
% 3.39/0.99  --bmc1_deadlock                         false
% 3.39/0.99  --bmc1_ucm                              false
% 3.39/0.99  --bmc1_add_unsat_core                   none
% 3.39/0.99  --bmc1_unsat_core_children              false
% 3.39/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/0.99  --bmc1_out_stat                         full
% 3.39/0.99  --bmc1_ground_init                      false
% 3.39/0.99  --bmc1_pre_inst_next_state              false
% 3.39/0.99  --bmc1_pre_inst_state                   false
% 3.39/0.99  --bmc1_pre_inst_reach_state             false
% 3.39/0.99  --bmc1_out_unsat_core                   false
% 3.39/0.99  --bmc1_aig_witness_out                  false
% 3.39/0.99  --bmc1_verbose                          false
% 3.39/0.99  --bmc1_dump_clauses_tptp                false
% 3.39/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.39/0.99  --bmc1_dump_file                        -
% 3.39/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.39/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.39/0.99  --bmc1_ucm_extend_mode                  1
% 3.39/0.99  --bmc1_ucm_init_mode                    2
% 3.39/0.99  --bmc1_ucm_cone_mode                    none
% 3.39/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.39/0.99  --bmc1_ucm_relax_model                  4
% 3.39/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.39/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/0.99  --bmc1_ucm_layered_model                none
% 3.39/0.99  --bmc1_ucm_max_lemma_size               10
% 3.39/0.99  
% 3.39/0.99  ------ AIG Options
% 3.39/0.99  
% 3.39/0.99  --aig_mode                              false
% 3.39/0.99  
% 3.39/0.99  ------ Instantiation Options
% 3.39/0.99  
% 3.39/0.99  --instantiation_flag                    true
% 3.39/0.99  --inst_sos_flag                         false
% 3.39/0.99  --inst_sos_phase                        true
% 3.39/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/0.99  --inst_lit_sel_side                     none
% 3.39/0.99  --inst_solver_per_active                1400
% 3.39/0.99  --inst_solver_calls_frac                1.
% 3.39/0.99  --inst_passive_queue_type               priority_queues
% 3.39/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/0.99  --inst_passive_queues_freq              [25;2]
% 3.39/0.99  --inst_dismatching                      true
% 3.39/0.99  --inst_eager_unprocessed_to_passive     true
% 3.39/0.99  --inst_prop_sim_given                   true
% 3.39/0.99  --inst_prop_sim_new                     false
% 3.39/0.99  --inst_subs_new                         false
% 3.39/0.99  --inst_eq_res_simp                      false
% 3.39/0.99  --inst_subs_given                       false
% 3.39/0.99  --inst_orphan_elimination               true
% 3.39/0.99  --inst_learning_loop_flag               true
% 3.39/0.99  --inst_learning_start                   3000
% 3.39/0.99  --inst_learning_factor                  2
% 3.39/0.99  --inst_start_prop_sim_after_learn       3
% 3.39/0.99  --inst_sel_renew                        solver
% 3.39/0.99  --inst_lit_activity_flag                true
% 3.39/0.99  --inst_restr_to_given                   false
% 3.39/0.99  --inst_activity_threshold               500
% 3.39/0.99  --inst_out_proof                        true
% 3.39/0.99  
% 3.39/0.99  ------ Resolution Options
% 3.39/0.99  
% 3.39/0.99  --resolution_flag                       false
% 3.39/0.99  --res_lit_sel                           adaptive
% 3.39/0.99  --res_lit_sel_side                      none
% 3.39/0.99  --res_ordering                          kbo
% 3.39/0.99  --res_to_prop_solver                    active
% 3.39/0.99  --res_prop_simpl_new                    false
% 3.39/0.99  --res_prop_simpl_given                  true
% 3.39/0.99  --res_passive_queue_type                priority_queues
% 3.39/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/0.99  --res_passive_queues_freq               [15;5]
% 3.39/0.99  --res_forward_subs                      full
% 3.39/0.99  --res_backward_subs                     full
% 3.39/0.99  --res_forward_subs_resolution           true
% 3.39/0.99  --res_backward_subs_resolution          true
% 3.39/0.99  --res_orphan_elimination                true
% 3.39/0.99  --res_time_limit                        2.
% 3.39/0.99  --res_out_proof                         true
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Options
% 3.39/0.99  
% 3.39/0.99  --superposition_flag                    true
% 3.39/0.99  --sup_passive_queue_type                priority_queues
% 3.39/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.39/0.99  --demod_completeness_check              fast
% 3.39/0.99  --demod_use_ground                      true
% 3.39/0.99  --sup_to_prop_solver                    passive
% 3.39/0.99  --sup_prop_simpl_new                    true
% 3.39/0.99  --sup_prop_simpl_given                  true
% 3.39/0.99  --sup_fun_splitting                     false
% 3.39/0.99  --sup_smt_interval                      50000
% 3.39/0.99  
% 3.39/0.99  ------ Superposition Simplification Setup
% 3.39/0.99  
% 3.39/0.99  --sup_indices_passive                   []
% 3.39/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_full_bw                           [BwDemod]
% 3.39/0.99  --sup_immed_triv                        [TrivRules]
% 3.39/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_immed_bw_main                     []
% 3.39/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/0.99  
% 3.39/0.99  ------ Combination Options
% 3.39/0.99  
% 3.39/0.99  --comb_res_mult                         3
% 3.39/0.99  --comb_sup_mult                         2
% 3.39/0.99  --comb_inst_mult                        10
% 3.39/0.99  
% 3.39/0.99  ------ Debug Options
% 3.39/0.99  
% 3.39/0.99  --dbg_backtrace                         false
% 3.39/0.99  --dbg_dump_prop_clauses                 false
% 3.39/0.99  --dbg_dump_prop_clauses_file            -
% 3.39/0.99  --dbg_out_stat                          false
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  ------ Proving...
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  % SZS status Theorem for theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  fof(f5,axiom,(
% 3.39/0.99    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f14,plain,(
% 3.39/0.99    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.39/0.99    inference(ennf_transformation,[],[f5])).
% 3.39/0.99  
% 3.39/0.99  fof(f29,plain,(
% 3.39/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 3.39/0.99    introduced(choice_axiom,[])).
% 3.39/0.99  
% 3.39/0.99  fof(f30,plain,(
% 3.39/0.99    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f29])).
% 3.39/0.99  
% 3.39/0.99  fof(f48,plain,(
% 3.39/0.99    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.39/0.99    inference(cnf_transformation,[],[f30])).
% 3.39/0.99  
% 3.39/0.99  fof(f3,axiom,(
% 3.39/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f46,plain,(
% 3.39/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f3])).
% 3.39/0.99  
% 3.39/0.99  fof(f4,axiom,(
% 3.39/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f47,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f4])).
% 3.39/0.99  
% 3.39/0.99  fof(f62,plain,(
% 3.39/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f46,f47])).
% 3.39/0.99  
% 3.39/0.99  fof(f70,plain,(
% 3.39/0.99    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 3.39/0.99    inference(definition_unfolding,[],[f48,f62])).
% 3.39/0.99  
% 3.39/0.99  fof(f8,axiom,(
% 3.39/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f17,plain,(
% 3.39/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 3.39/0.99    inference(ennf_transformation,[],[f8])).
% 3.39/0.99  
% 3.39/0.99  fof(f32,plain,(
% 3.39/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 3.39/0.99    inference(nnf_transformation,[],[f17])).
% 3.39/0.99  
% 3.39/0.99  fof(f54,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f32])).
% 3.39/0.99  
% 3.39/0.99  fof(f10,conjecture,(
% 3.39/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f11,negated_conjecture,(
% 3.39/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.39/0.99    inference(negated_conjecture,[],[f10])).
% 3.39/0.99  
% 3.39/0.99  fof(f20,plain,(
% 3.39/0.99    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.39/0.99    inference(ennf_transformation,[],[f11])).
% 3.39/0.99  
% 3.39/0.99  fof(f21,plain,(
% 3.39/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.39/0.99    inference(flattening,[],[f20])).
% 3.39/0.99  
% 3.39/0.99  fof(f35,plain,(
% 3.39/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k11_relat_1(X1,X0) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.39/0.99    introduced(choice_axiom,[])).
% 3.39/0.99  
% 3.39/0.99  fof(f36,plain,(
% 3.39/0.99    k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) & r2_hidden(sK3,k1_relat_1(sK4)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f35])).
% 3.39/0.99  
% 3.39/0.99  fof(f58,plain,(
% 3.39/0.99    v1_relat_1(sK4)),
% 3.39/0.99    inference(cnf_transformation,[],[f36])).
% 3.39/0.99  
% 3.39/0.99  fof(f9,axiom,(
% 3.39/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f18,plain,(
% 3.39/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.39/0.99    inference(ennf_transformation,[],[f9])).
% 3.39/0.99  
% 3.39/0.99  fof(f19,plain,(
% 3.39/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.39/0.99    inference(flattening,[],[f18])).
% 3.39/0.99  
% 3.39/0.99  fof(f33,plain,(
% 3.39/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.39/0.99    inference(nnf_transformation,[],[f19])).
% 3.39/0.99  
% 3.39/0.99  fof(f34,plain,(
% 3.39/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.39/0.99    inference(flattening,[],[f33])).
% 3.39/0.99  
% 3.39/0.99  fof(f56,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f34])).
% 3.39/0.99  
% 3.39/0.99  fof(f59,plain,(
% 3.39/0.99    v1_funct_1(sK4)),
% 3.39/0.99    inference(cnf_transformation,[],[f36])).
% 3.39/0.99  
% 3.39/0.99  fof(f61,plain,(
% 3.39/0.99    k1_tarski(k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)),
% 3.39/0.99    inference(cnf_transformation,[],[f36])).
% 3.39/0.99  
% 3.39/0.99  fof(f72,plain,(
% 3.39/0.99    k1_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3)),
% 3.39/0.99    inference(definition_unfolding,[],[f61,f62])).
% 3.39/0.99  
% 3.39/0.99  fof(f49,plain,(
% 3.39/0.99    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.39/0.99    inference(cnf_transformation,[],[f30])).
% 3.39/0.99  
% 3.39/0.99  fof(f69,plain,(
% 3.39/0.99    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 3.39/0.99    inference(definition_unfolding,[],[f49,f62])).
% 3.39/0.99  
% 3.39/0.99  fof(f6,axiom,(
% 3.39/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f15,plain,(
% 3.39/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.39/0.99    inference(ennf_transformation,[],[f6])).
% 3.39/0.99  
% 3.39/0.99  fof(f50,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f15])).
% 3.39/0.99  
% 3.39/0.99  fof(f71,plain,(
% 3.39/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.39/0.99    inference(definition_unfolding,[],[f50,f62])).
% 3.39/0.99  
% 3.39/0.99  fof(f7,axiom,(
% 3.39/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f16,plain,(
% 3.39/0.99    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.39/0.99    inference(ennf_transformation,[],[f7])).
% 3.39/0.99  
% 3.39/0.99  fof(f31,plain,(
% 3.39/0.99    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.39/0.99    inference(nnf_transformation,[],[f16])).
% 3.39/0.99  
% 3.39/0.99  fof(f51,plain,(
% 3.39/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f31])).
% 3.39/0.99  
% 3.39/0.99  fof(f2,axiom,(
% 3.39/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f24,plain,(
% 3.39/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.39/0.99    inference(nnf_transformation,[],[f2])).
% 3.39/0.99  
% 3.39/0.99  fof(f25,plain,(
% 3.39/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.39/0.99    inference(flattening,[],[f24])).
% 3.39/0.99  
% 3.39/0.99  fof(f26,plain,(
% 3.39/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.39/0.99    inference(rectify,[],[f25])).
% 3.39/0.99  
% 3.39/0.99  fof(f27,plain,(
% 3.39/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.39/0.99    introduced(choice_axiom,[])).
% 3.39/0.99  
% 3.39/0.99  fof(f28,plain,(
% 3.39/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.39/0.99  
% 3.39/0.99  fof(f42,plain,(
% 3.39/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.39/0.99    inference(cnf_transformation,[],[f28])).
% 3.39/0.99  
% 3.39/0.99  fof(f66,plain,(
% 3.39/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.39/0.99    inference(definition_unfolding,[],[f42,f47])).
% 3.39/0.99  
% 3.39/0.99  fof(f73,plain,(
% 3.39/0.99    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 3.39/0.99    inference(equality_resolution,[],[f66])).
% 3.39/0.99  
% 3.39/0.99  fof(f74,plain,(
% 3.39/0.99    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 3.39/0.99    inference(equality_resolution,[],[f73])).
% 3.39/0.99  
% 3.39/0.99  fof(f1,axiom,(
% 3.39/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/0.99  
% 3.39/0.99  fof(f12,plain,(
% 3.39/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.39/0.99    inference(rectify,[],[f1])).
% 3.39/0.99  
% 3.39/0.99  fof(f13,plain,(
% 3.39/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.39/0.99    inference(ennf_transformation,[],[f12])).
% 3.39/0.99  
% 3.39/0.99  fof(f22,plain,(
% 3.39/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.39/0.99    introduced(choice_axiom,[])).
% 3.39/0.99  
% 3.39/0.99  fof(f23,plain,(
% 3.39/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f22])).
% 3.39/0.99  
% 3.39/0.99  fof(f39,plain,(
% 3.39/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.39/0.99    inference(cnf_transformation,[],[f23])).
% 3.39/0.99  
% 3.39/0.99  fof(f60,plain,(
% 3.39/0.99    r2_hidden(sK3,k1_relat_1(sK4))),
% 3.39/0.99    inference(cnf_transformation,[],[f36])).
% 3.39/0.99  
% 3.39/0.99  cnf(c_10,plain,
% 3.39/0.99      ( r2_hidden(sK2(X0,X1),X0)
% 3.39/0.99      | k1_enumset1(X1,X1,X1) = X0
% 3.39/0.99      | k1_xboole_0 = X0 ),
% 3.39/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1166,plain,
% 3.39/0.99      ( k1_enumset1(X0,X0,X0) = X1
% 3.39/0.99      | k1_xboole_0 = X1
% 3.39/0.99      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_14,plain,
% 3.39/0.99      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 3.39/0.99      | r2_hidden(k4_tarski(X2,X0),X1)
% 3.39/0.99      | ~ v1_relat_1(X1) ),
% 3.39/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_22,negated_conjecture,
% 3.39/0.99      ( v1_relat_1(sK4) ),
% 3.39/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_343,plain,
% 3.39/0.99      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 3.39/0.99      | r2_hidden(k4_tarski(X2,X0),X1)
% 3.39/0.99      | sK4 != X1 ),
% 3.39/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_344,plain,
% 3.39/0.99      ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
% 3.39/0.99      | r2_hidden(k4_tarski(X1,X0),sK4) ),
% 3.39/0.99      inference(unflattening,[status(thm)],[c_343]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_516,plain,
% 3.39/0.99      ( r2_hidden(k4_tarski(X1,X0),sK4)
% 3.39/0.99      | ~ r2_hidden(X0,k11_relat_1(sK4,X1)) ),
% 3.39/0.99      inference(prop_impl,[status(thm)],[c_344]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_517,plain,
% 3.39/0.99      ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
% 3.39/0.99      | r2_hidden(k4_tarski(X1,X0),sK4) ),
% 3.39/0.99      inference(renaming,[status(thm)],[c_516]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1158,plain,
% 3.39/0.99      ( r2_hidden(X0,k11_relat_1(sK4,X1)) != iProver_top
% 3.39/0.99      | r2_hidden(k4_tarski(X1,X0),sK4) = iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_517]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_2450,plain,
% 3.39/0.99      ( k1_enumset1(X0,X0,X0) = k11_relat_1(sK4,X1)
% 3.39/0.99      | k11_relat_1(sK4,X1) = k1_xboole_0
% 3.39/0.99      | r2_hidden(k4_tarski(X1,sK2(k11_relat_1(sK4,X1),X0)),sK4) = iProver_top ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_1166,c_1158]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_17,plain,
% 3.39/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.39/0.99      | ~ v1_funct_1(X2)
% 3.39/0.99      | ~ v1_relat_1(X2)
% 3.39/0.99      | k1_funct_1(X2,X0) = X1 ),
% 3.39/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_21,negated_conjecture,
% 3.39/0.99      ( v1_funct_1(sK4) ),
% 3.39/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_238,plain,
% 3.39/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.39/0.99      | ~ v1_relat_1(X2)
% 3.39/0.99      | k1_funct_1(X2,X0) = X1
% 3.39/0.99      | sK4 != X2 ),
% 3.39/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_239,plain,
% 3.39/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 3.39/0.99      | ~ v1_relat_1(sK4)
% 3.39/0.99      | k1_funct_1(sK4,X0) = X1 ),
% 3.39/0.99      inference(unflattening,[status(thm)],[c_238]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_243,plain,
% 3.39/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK4) | k1_funct_1(sK4,X0) = X1 ),
% 3.39/0.99      inference(global_propositional_subsumption,
% 3.39/0.99                [status(thm)],
% 3.39/0.99                [c_239,c_22]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1164,plain,
% 3.39/0.99      ( k1_funct_1(sK4,X0) = X1
% 3.39/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_5942,plain,
% 3.39/0.99      ( k1_enumset1(X0,X0,X0) = k11_relat_1(sK4,X1)
% 3.39/0.99      | k11_relat_1(sK4,X1) = k1_xboole_0
% 3.39/0.99      | sK2(k11_relat_1(sK4,X1),X0) = k1_funct_1(sK4,X1) ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_2450,c_1164]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_19,negated_conjecture,
% 3.39/0.99      ( k1_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k11_relat_1(sK4,sK3) ),
% 3.39/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_6503,plain,
% 3.39/0.99      ( k11_relat_1(sK4,X0) != k11_relat_1(sK4,sK3)
% 3.39/0.99      | k11_relat_1(sK4,X0) = k1_xboole_0
% 3.39/0.99      | sK2(k11_relat_1(sK4,X0),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,X0) ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_5942,c_19]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_6877,plain,
% 3.39/0.99      ( k11_relat_1(sK4,sK3) = k1_xboole_0
% 3.39/0.99      | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,sK3) ),
% 3.39/0.99      inference(equality_resolution,[status(thm)],[c_6503]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_9,plain,
% 3.39/0.99      ( k1_enumset1(X0,X0,X0) = X1
% 3.39/0.99      | sK2(X1,X0) != X0
% 3.39/0.99      | k1_xboole_0 = X1 ),
% 3.39/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1387,plain,
% 3.39/0.99      ( k1_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k11_relat_1(sK4,sK3)
% 3.39/0.99      | sK2(k11_relat_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k1_funct_1(sK4,sK3)
% 3.39/0.99      | k1_xboole_0 = k11_relat_1(sK4,sK3) ),
% 3.39/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_703,plain,( X0 = X0 ),theory(equality) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1971,plain,
% 3.39/0.99      ( k11_relat_1(sK4,sK3) = k11_relat_1(sK4,sK3) ),
% 3.39/0.99      inference(instantiation,[status(thm)],[c_703]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_704,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1485,plain,
% 3.39/0.99      ( X0 != X1
% 3.39/0.99      | k11_relat_1(sK4,sK3) != X1
% 3.39/0.99      | k11_relat_1(sK4,sK3) = X0 ),
% 3.39/0.99      inference(instantiation,[status(thm)],[c_704]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1970,plain,
% 3.39/0.99      ( X0 != k11_relat_1(sK4,sK3)
% 3.39/0.99      | k11_relat_1(sK4,sK3) = X0
% 3.39/0.99      | k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3) ),
% 3.39/0.99      inference(instantiation,[status(thm)],[c_1485]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_3490,plain,
% 3.39/0.99      ( k11_relat_1(sK4,sK3) != k11_relat_1(sK4,sK3)
% 3.39/0.99      | k11_relat_1(sK4,sK3) = k1_xboole_0
% 3.39/0.99      | k1_xboole_0 != k11_relat_1(sK4,sK3) ),
% 3.39/0.99      inference(instantiation,[status(thm)],[c_1970]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_7072,plain,
% 3.39/0.99      ( k11_relat_1(sK4,sK3) = k1_xboole_0 ),
% 3.39/0.99      inference(global_propositional_subsumption,
% 3.39/0.99                [status(thm)],
% 3.39/0.99                [c_6877,c_19,c_1387,c_1971,c_3490]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_11,plain,
% 3.39/0.99      ( ~ v1_relat_1(X0)
% 3.39/0.99      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.39/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_325,plain,
% 3.39/0.99      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.39/0.99      | sK4 != X0 ),
% 3.39/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_326,plain,
% 3.39/0.99      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 3.39/0.99      inference(unflattening,[status(thm)],[c_325]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_13,plain,
% 3.39/0.99      ( r1_xboole_0(k1_relat_1(X0),X1)
% 3.39/0.99      | ~ v1_relat_1(X0)
% 3.39/0.99      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 3.39/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_301,plain,
% 3.39/0.99      ( r1_xboole_0(k1_relat_1(X0),X1)
% 3.39/0.99      | k9_relat_1(X0,X1) != k1_xboole_0
% 3.39/0.99      | sK4 != X0 ),
% 3.39/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_302,plain,
% 3.39/0.99      ( r1_xboole_0(k1_relat_1(sK4),X0)
% 3.39/0.99      | k9_relat_1(sK4,X0) != k1_xboole_0 ),
% 3.39/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_512,plain,
% 3.39/0.99      ( r1_xboole_0(k1_relat_1(sK4),X0)
% 3.39/0.99      | k9_relat_1(sK4,X0) != k1_xboole_0 ),
% 3.39/0.99      inference(prop_impl,[status(thm)],[c_302]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1161,plain,
% 3.39/0.99      ( k9_relat_1(sK4,X0) != k1_xboole_0
% 3.39/0.99      | r1_xboole_0(k1_relat_1(sK4),X0) = iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1703,plain,
% 3.39/0.99      ( k11_relat_1(sK4,X0) != k1_xboole_0
% 3.39/0.99      | r1_xboole_0(k1_relat_1(sK4),k1_enumset1(X0,X0,X0)) = iProver_top ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_326,c_1161]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_7144,plain,
% 3.39/0.99      ( r1_xboole_0(k1_relat_1(sK4),k1_enumset1(sK3,sK3,sK3)) = iProver_top ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_7072,c_1703]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_6,plain,
% 3.39/0.99      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 3.39/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1169,plain,
% 3.39/0.99      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_0,plain,
% 3.39/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.39/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_1175,plain,
% 3.39/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.39/0.99      | r2_hidden(X0,X2) != iProver_top
% 3.39/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_2120,plain,
% 3.39/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.39/0.99      | r1_xboole_0(X1,k1_enumset1(X2,X2,X0)) != iProver_top ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_1169,c_1175]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_8831,plain,
% 3.39/0.99      ( r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
% 3.39/0.99      inference(superposition,[status(thm)],[c_7144,c_2120]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_20,negated_conjecture,
% 3.39/0.99      ( r2_hidden(sK3,k1_relat_1(sK4)) ),
% 3.39/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(c_25,plain,
% 3.39/0.99      ( r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
% 3.39/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.39/0.99  
% 3.39/0.99  cnf(contradiction,plain,
% 3.39/0.99      ( $false ),
% 3.39/0.99      inference(minisat,[status(thm)],[c_8831,c_25]) ).
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  ------                               Statistics
% 3.39/0.99  
% 3.39/0.99  ------ General
% 3.39/0.99  
% 3.39/0.99  abstr_ref_over_cycles:                  0
% 3.39/0.99  abstr_ref_under_cycles:                 0
% 3.39/0.99  gc_basic_clause_elim:                   0
% 3.39/0.99  forced_gc_time:                         0
% 3.39/0.99  parsing_time:                           0.009
% 3.39/0.99  unif_index_cands_time:                  0.
% 3.39/0.99  unif_index_add_time:                    0.
% 3.39/0.99  orderings_time:                         0.
% 3.39/0.99  out_proof_time:                         0.007
% 3.39/0.99  total_time:                             0.248
% 3.39/0.99  num_of_symbols:                         47
% 3.39/0.99  num_of_terms:                           11058
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing
% 3.39/0.99  
% 3.39/0.99  num_of_splits:                          0
% 3.39/0.99  num_of_split_atoms:                     0
% 3.39/0.99  num_of_reused_defs:                     0
% 3.39/0.99  num_eq_ax_congr_red:                    28
% 3.39/0.99  num_of_sem_filtered_clauses:            1
% 3.39/0.99  num_of_subtypes:                        0
% 3.39/0.99  monotx_restored_types:                  0
% 3.39/0.99  sat_num_of_epr_types:                   0
% 3.39/0.99  sat_num_of_non_cyclic_types:            0
% 3.39/0.99  sat_guarded_non_collapsed_types:        0
% 3.39/0.99  num_pure_diseq_elim:                    0
% 3.39/0.99  simp_replaced_by:                       0
% 3.39/0.99  res_preprocessed:                       107
% 3.39/0.99  prep_upred:                             0
% 3.39/0.99  prep_unflattend:                        28
% 3.39/0.99  smt_new_axioms:                         0
% 3.39/0.99  pred_elim_cands:                        2
% 3.39/0.99  pred_elim:                              2
% 3.39/0.99  pred_elim_cl:                           2
% 3.39/0.99  pred_elim_cycles:                       4
% 3.39/0.99  merged_defs:                            12
% 3.39/0.99  merged_defs_ncl:                        0
% 3.39/0.99  bin_hyper_res:                          12
% 3.39/0.99  prep_cycles:                            4
% 3.39/0.99  pred_elim_time:                         0.004
% 3.39/0.99  splitting_time:                         0.
% 3.39/0.99  sem_filter_time:                        0.
% 3.39/0.99  monotx_time:                            0.
% 3.39/0.99  subtype_inf_time:                       0.
% 3.39/0.99  
% 3.39/0.99  ------ Problem properties
% 3.39/0.99  
% 3.39/0.99  clauses:                                21
% 3.39/0.99  conjectures:                            2
% 3.39/0.99  epr:                                    1
% 3.39/0.99  horn:                                   15
% 3.39/0.99  ground:                                 2
% 3.39/0.99  unary:                                  5
% 3.39/0.99  binary:                                 9
% 3.39/0.99  lits:                                   45
% 3.39/0.99  lits_eq:                                19
% 3.39/0.99  fd_pure:                                0
% 3.39/0.99  fd_pseudo:                              0
% 3.39/0.99  fd_cond:                                0
% 3.39/0.99  fd_pseudo_cond:                         6
% 3.39/0.99  ac_symbols:                             0
% 3.39/0.99  
% 3.39/0.99  ------ Propositional Solver
% 3.39/0.99  
% 3.39/0.99  prop_solver_calls:                      27
% 3.39/0.99  prop_fast_solver_calls:                 727
% 3.39/0.99  smt_solver_calls:                       0
% 3.39/0.99  smt_fast_solver_calls:                  0
% 3.39/0.99  prop_num_of_clauses:                    3817
% 3.39/0.99  prop_preprocess_simplified:             8510
% 3.39/0.99  prop_fo_subsumed:                       9
% 3.39/0.99  prop_solver_time:                       0.
% 3.39/0.99  smt_solver_time:                        0.
% 3.39/0.99  smt_fast_solver_time:                   0.
% 3.39/0.99  prop_fast_solver_time:                  0.
% 3.39/0.99  prop_unsat_core_time:                   0.
% 3.39/0.99  
% 3.39/0.99  ------ QBF
% 3.39/0.99  
% 3.39/0.99  qbf_q_res:                              0
% 3.39/0.99  qbf_num_tautologies:                    0
% 3.39/0.99  qbf_prep_cycles:                        0
% 3.39/0.99  
% 3.39/0.99  ------ BMC1
% 3.39/0.99  
% 3.39/0.99  bmc1_current_bound:                     -1
% 3.39/0.99  bmc1_last_solved_bound:                 -1
% 3.39/0.99  bmc1_unsat_core_size:                   -1
% 3.39/0.99  bmc1_unsat_core_parents_size:           -1
% 3.39/0.99  bmc1_merge_next_fun:                    0
% 3.39/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.39/0.99  
% 3.39/0.99  ------ Instantiation
% 3.39/0.99  
% 3.39/0.99  inst_num_of_clauses:                    980
% 3.39/0.99  inst_num_in_passive:                    220
% 3.39/0.99  inst_num_in_active:                     340
% 3.39/0.99  inst_num_in_unprocessed:                420
% 3.39/0.99  inst_num_of_loops:                      390
% 3.39/0.99  inst_num_of_learning_restarts:          0
% 3.39/0.99  inst_num_moves_active_passive:          49
% 3.39/0.99  inst_lit_activity:                      0
% 3.39/0.99  inst_lit_activity_moves:                0
% 3.39/0.99  inst_num_tautologies:                   0
% 3.39/0.99  inst_num_prop_implied:                  0
% 3.39/0.99  inst_num_existing_simplified:           0
% 3.39/0.99  inst_num_eq_res_simplified:             0
% 3.39/0.99  inst_num_child_elim:                    0
% 3.39/0.99  inst_num_of_dismatching_blockings:      514
% 3.39/0.99  inst_num_of_non_proper_insts:           706
% 3.39/0.99  inst_num_of_duplicates:                 0
% 3.39/0.99  inst_inst_num_from_inst_to_res:         0
% 3.39/0.99  inst_dismatching_checking_time:         0.
% 3.39/0.99  
% 3.39/0.99  ------ Resolution
% 3.39/0.99  
% 3.39/0.99  res_num_of_clauses:                     0
% 3.39/0.99  res_num_in_passive:                     0
% 3.39/0.99  res_num_in_active:                      0
% 3.39/0.99  res_num_of_loops:                       111
% 3.39/0.99  res_forward_subset_subsumed:            85
% 3.39/0.99  res_backward_subset_subsumed:           0
% 3.39/0.99  res_forward_subsumed:                   0
% 3.39/0.99  res_backward_subsumed:                  0
% 3.39/0.99  res_forward_subsumption_resolution:     0
% 3.39/0.99  res_backward_subsumption_resolution:    0
% 3.39/0.99  res_clause_to_clause_subsumption:       545
% 3.39/0.99  res_orphan_elimination:                 0
% 3.39/0.99  res_tautology_del:                      62
% 3.39/0.99  res_num_eq_res_simplified:              0
% 3.39/0.99  res_num_sel_changes:                    0
% 3.39/0.99  res_moves_from_active_to_pass:          0
% 3.39/0.99  
% 3.39/0.99  ------ Superposition
% 3.39/0.99  
% 3.39/0.99  sup_time_total:                         0.
% 3.39/0.99  sup_time_generating:                    0.
% 3.39/0.99  sup_time_sim_full:                      0.
% 3.39/0.99  sup_time_sim_immed:                     0.
% 3.39/0.99  
% 3.39/0.99  sup_num_of_clauses:                     199
% 3.39/0.99  sup_num_in_active:                      62
% 3.39/0.99  sup_num_in_passive:                     137
% 3.39/0.99  sup_num_of_loops:                       76
% 3.39/0.99  sup_fw_superposition:                   85
% 3.39/0.99  sup_bw_superposition:                   185
% 3.39/0.99  sup_immediate_simplified:               48
% 3.39/0.99  sup_given_eliminated:                   0
% 3.39/0.99  comparisons_done:                       0
% 3.39/0.99  comparisons_avoided:                    14
% 3.39/0.99  
% 3.39/0.99  ------ Simplifications
% 3.39/0.99  
% 3.39/0.99  
% 3.39/0.99  sim_fw_subset_subsumed:                 20
% 3.39/0.99  sim_bw_subset_subsumed:                 3
% 3.39/0.99  sim_fw_subsumed:                        9
% 3.39/0.99  sim_bw_subsumed:                        0
% 3.39/0.99  sim_fw_subsumption_res:                 0
% 3.39/0.99  sim_bw_subsumption_res:                 0
% 3.39/0.99  sim_tautology_del:                      5
% 3.39/0.99  sim_eq_tautology_del:                   3
% 3.39/0.99  sim_eq_res_simp:                        0
% 3.39/0.99  sim_fw_demodulated:                     1
% 3.39/0.99  sim_bw_demodulated:                     16
% 3.39/0.99  sim_light_normalised:                   18
% 3.39/0.99  sim_joinable_taut:                      0
% 3.39/0.99  sim_joinable_simp:                      0
% 3.39/0.99  sim_ac_normalised:                      0
% 3.39/0.99  sim_smt_subsumption:                    0
% 3.39/0.99  
%------------------------------------------------------------------------------
