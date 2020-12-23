%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:14 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 445 expanded)
%              Number of clauses        :   53 (  93 expanded)
%              Number of leaves         :   17 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  403 (1292 expanded)
%              Number of equality atoms :  246 ( 792 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f44,f73])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK4,sK3)) != k2_relat_1(sK4)
      & k1_tarski(sK3) = k1_relat_1(sK4)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k1_tarski(k1_funct_1(sK4,sK3)) != k2_relat_1(sK4)
    & k1_tarski(sK3) = k1_relat_1(sK4)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f38])).

fof(f69,plain,(
    k1_tarski(sK3) = k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK4) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f73])).

fof(f67,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f36])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f24,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4) != X0
            & sK2(X0,X1,X2,X3,X4) != X1
            & sK2(X0,X1,X2,X3,X4) != X2
            & sK2(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & ( sK2(X0,X1,X2,X3,X4) = X0
          | sK2(X0,X1,X2,X3,X4) = X1
          | sK2(X0,X1,X2,X3,X4) = X2
          | sK2(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK2(X0,X1,X2,X3,X4) != X0
              & sK2(X0,X1,X2,X3,X4) != X1
              & sK2(X0,X1,X2,X3,X4) != X2
              & sK2(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & ( sK2(X0,X1,X2,X3,X4) = X0
            | sK2(X0,X1,X2,X3,X4) = X1
            | sK2(X0,X1,X2,X3,X4) = X2
            | sK2(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X0 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    ! [X6,X4,X2,X3,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X6,X1,X2,X3,X4) ) ),
    inference(equality_resolution,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f15,f24])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k3_enumset1(X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f56,f43])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k3_enumset1(X0,X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f77])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    k1_tarski(k1_funct_1(sK4,sK3)) != k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    k3_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k2_relat_1(sK4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f45,f73])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2471,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,negated_conjecture,
    ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_340,plain,
    ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_341,plain,
    ( k9_relat_1(sK4,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_2661,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_24,c_341])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_335,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_336,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_2662,plain,
    ( k11_relat_1(sK4,sK3) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2661,c_336])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_382,plain,
    ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_1160,plain,
    ( r2_hidden(k4_tarski(X1,X0),sK4)
    | ~ r2_hidden(X0,k11_relat_1(sK4,X1)) ),
    inference(prop_impl,[status(thm)],[c_383])).

cnf(c_1161,plain,
    ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(renaming,[status(thm)],[c_1160])).

cnf(c_2452,plain,
    ( r2_hidden(X0,k11_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_2893,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(sK3,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2662,c_2452])).

cnf(c_21,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_272,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_273,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_26])).

cnf(c_2458,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_3126,plain,
    ( k1_funct_1(sK4,sK3) = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2893,c_2458])).

cnf(c_3651,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK4)
    | sK1(k2_relat_1(sK4),X0) = k1_funct_1(sK4,sK3)
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2471,c_3126])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | r2_hidden(X0,X4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2785,plain,
    ( ~ sP0(X0,X1,X2,X3,k1_relat_1(sK4))
    | r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2786,plain,
    ( sP0(X0,X1,X2,X3,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2785])).

cnf(c_2788,plain,
    ( sP0(sK3,sK3,sK3,sK3,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2459,plain,
    ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2943,plain,
    ( sP0(sK3,sK3,sK3,sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_2459])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | k11_relat_1(X1,X0) != k1_xboole_0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_347,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k11_relat_1(sK4,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_1156,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | k11_relat_1(sK4,X0) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_347])).

cnf(c_2455,plain,
    ( k11_relat_1(sK4,X0) != k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_3362,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2662,c_2455])).

cnf(c_3847,plain,
    ( sK1(k2_relat_1(sK4),X0) = k1_funct_1(sK4,sK3)
    | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3651,c_2788,c_2943,c_3362])).

cnf(c_3848,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK4)
    | sK1(k2_relat_1(sK4),X0) = k1_funct_1(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_3847])).

cnf(c_23,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k2_relat_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3856,plain,
    ( sK1(k2_relat_1(sK4),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_3848,c_23])).

cnf(c_1946,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2646,plain,
    ( k11_relat_1(sK4,X0) != X1
    | k11_relat_1(sK4,X0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1946])).

cnf(c_2934,plain,
    ( k11_relat_1(sK4,X0) != k2_relat_1(sK4)
    | k11_relat_1(sK4,X0) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_2935,plain,
    ( k11_relat_1(sK4,sK3) != k2_relat_1(sK4)
    | k11_relat_1(sK4,sK3) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2934])).

cnf(c_0,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2663,plain,
    ( k3_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k2_relat_1(sK4)
    | sK1(k2_relat_1(sK4),k1_funct_1(sK4,sK3)) != k1_funct_1(sK4,sK3)
    | k1_xboole_0 = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_348,plain,
    ( k11_relat_1(sK4,X0) != k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_350,plain,
    ( k11_relat_1(sK4,sK3) != k1_xboole_0
    | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3856,c_2943,c_2935,c_2788,c_2663,c_2662,c_350,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.72/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/1.01  
% 2.72/1.01  ------  iProver source info
% 2.72/1.01  
% 2.72/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.72/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/1.01  git: non_committed_changes: false
% 2.72/1.01  git: last_make_outside_of_git: false
% 2.72/1.01  
% 2.72/1.01  ------ 
% 2.72/1.01  
% 2.72/1.01  ------ Input Options
% 2.72/1.01  
% 2.72/1.01  --out_options                           all
% 2.72/1.01  --tptp_safe_out                         true
% 2.72/1.01  --problem_path                          ""
% 2.72/1.01  --include_path                          ""
% 2.72/1.01  --clausifier                            res/vclausify_rel
% 2.72/1.01  --clausifier_options                    --mode clausify
% 2.72/1.01  --stdin                                 false
% 2.72/1.01  --stats_out                             all
% 2.72/1.01  
% 2.72/1.01  ------ General Options
% 2.72/1.01  
% 2.72/1.01  --fof                                   false
% 2.72/1.01  --time_out_real                         305.
% 2.72/1.01  --time_out_virtual                      -1.
% 2.72/1.01  --symbol_type_check                     false
% 2.72/1.01  --clausify_out                          false
% 2.72/1.01  --sig_cnt_out                           false
% 2.72/1.01  --trig_cnt_out                          false
% 2.72/1.01  --trig_cnt_out_tolerance                1.
% 2.72/1.01  --trig_cnt_out_sk_spl                   false
% 2.72/1.01  --abstr_cl_out                          false
% 2.72/1.01  
% 2.72/1.01  ------ Global Options
% 2.72/1.01  
% 2.72/1.01  --schedule                              default
% 2.72/1.01  --add_important_lit                     false
% 2.72/1.01  --prop_solver_per_cl                    1000
% 2.72/1.01  --min_unsat_core                        false
% 2.72/1.01  --soft_assumptions                      false
% 2.72/1.01  --soft_lemma_size                       3
% 2.72/1.01  --prop_impl_unit_size                   0
% 2.72/1.01  --prop_impl_unit                        []
% 2.72/1.01  --share_sel_clauses                     true
% 2.72/1.01  --reset_solvers                         false
% 2.72/1.01  --bc_imp_inh                            [conj_cone]
% 2.72/1.01  --conj_cone_tolerance                   3.
% 2.72/1.01  --extra_neg_conj                        none
% 2.72/1.01  --large_theory_mode                     true
% 2.72/1.01  --prolific_symb_bound                   200
% 2.72/1.01  --lt_threshold                          2000
% 2.72/1.01  --clause_weak_htbl                      true
% 2.72/1.01  --gc_record_bc_elim                     false
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing Options
% 2.72/1.01  
% 2.72/1.01  --preprocessing_flag                    true
% 2.72/1.01  --time_out_prep_mult                    0.1
% 2.72/1.01  --splitting_mode                        input
% 2.72/1.01  --splitting_grd                         true
% 2.72/1.01  --splitting_cvd                         false
% 2.72/1.01  --splitting_cvd_svl                     false
% 2.72/1.01  --splitting_nvd                         32
% 2.72/1.01  --sub_typing                            true
% 2.72/1.01  --prep_gs_sim                           true
% 2.72/1.01  --prep_unflatten                        true
% 2.72/1.01  --prep_res_sim                          true
% 2.72/1.01  --prep_upred                            true
% 2.72/1.01  --prep_sem_filter                       exhaustive
% 2.72/1.01  --prep_sem_filter_out                   false
% 2.72/1.01  --pred_elim                             true
% 2.72/1.01  --res_sim_input                         true
% 2.72/1.01  --eq_ax_congr_red                       true
% 2.72/1.01  --pure_diseq_elim                       true
% 2.72/1.01  --brand_transform                       false
% 2.72/1.01  --non_eq_to_eq                          false
% 2.72/1.01  --prep_def_merge                        true
% 2.72/1.01  --prep_def_merge_prop_impl              false
% 2.72/1.01  --prep_def_merge_mbd                    true
% 2.72/1.01  --prep_def_merge_tr_red                 false
% 2.72/1.01  --prep_def_merge_tr_cl                  false
% 2.72/1.01  --smt_preprocessing                     true
% 2.72/1.01  --smt_ac_axioms                         fast
% 2.72/1.01  --preprocessed_out                      false
% 2.72/1.01  --preprocessed_stats                    false
% 2.72/1.01  
% 2.72/1.01  ------ Abstraction refinement Options
% 2.72/1.01  
% 2.72/1.01  --abstr_ref                             []
% 2.72/1.01  --abstr_ref_prep                        false
% 2.72/1.01  --abstr_ref_until_sat                   false
% 2.72/1.01  --abstr_ref_sig_restrict                funpre
% 2.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/1.01  --abstr_ref_under                       []
% 2.72/1.01  
% 2.72/1.01  ------ SAT Options
% 2.72/1.01  
% 2.72/1.01  --sat_mode                              false
% 2.72/1.01  --sat_fm_restart_options                ""
% 2.72/1.01  --sat_gr_def                            false
% 2.72/1.01  --sat_epr_types                         true
% 2.72/1.01  --sat_non_cyclic_types                  false
% 2.72/1.01  --sat_finite_models                     false
% 2.72/1.01  --sat_fm_lemmas                         false
% 2.72/1.01  --sat_fm_prep                           false
% 2.72/1.01  --sat_fm_uc_incr                        true
% 2.72/1.01  --sat_out_model                         small
% 2.72/1.01  --sat_out_clauses                       false
% 2.72/1.01  
% 2.72/1.01  ------ QBF Options
% 2.72/1.01  
% 2.72/1.01  --qbf_mode                              false
% 2.72/1.01  --qbf_elim_univ                         false
% 2.72/1.01  --qbf_dom_inst                          none
% 2.72/1.01  --qbf_dom_pre_inst                      false
% 2.72/1.01  --qbf_sk_in                             false
% 2.72/1.01  --qbf_pred_elim                         true
% 2.72/1.01  --qbf_split                             512
% 2.72/1.01  
% 2.72/1.01  ------ BMC1 Options
% 2.72/1.01  
% 2.72/1.01  --bmc1_incremental                      false
% 2.72/1.01  --bmc1_axioms                           reachable_all
% 2.72/1.01  --bmc1_min_bound                        0
% 2.72/1.01  --bmc1_max_bound                        -1
% 2.72/1.01  --bmc1_max_bound_default                -1
% 2.72/1.01  --bmc1_symbol_reachability              true
% 2.72/1.01  --bmc1_property_lemmas                  false
% 2.72/1.01  --bmc1_k_induction                      false
% 2.72/1.01  --bmc1_non_equiv_states                 false
% 2.72/1.01  --bmc1_deadlock                         false
% 2.72/1.01  --bmc1_ucm                              false
% 2.72/1.01  --bmc1_add_unsat_core                   none
% 2.72/1.01  --bmc1_unsat_core_children              false
% 2.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/1.01  --bmc1_out_stat                         full
% 2.72/1.01  --bmc1_ground_init                      false
% 2.72/1.01  --bmc1_pre_inst_next_state              false
% 2.72/1.01  --bmc1_pre_inst_state                   false
% 2.72/1.01  --bmc1_pre_inst_reach_state             false
% 2.72/1.01  --bmc1_out_unsat_core                   false
% 2.72/1.01  --bmc1_aig_witness_out                  false
% 2.72/1.01  --bmc1_verbose                          false
% 2.72/1.01  --bmc1_dump_clauses_tptp                false
% 2.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.72/1.01  --bmc1_dump_file                        -
% 2.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.72/1.01  --bmc1_ucm_extend_mode                  1
% 2.72/1.01  --bmc1_ucm_init_mode                    2
% 2.72/1.01  --bmc1_ucm_cone_mode                    none
% 2.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.72/1.01  --bmc1_ucm_relax_model                  4
% 2.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/1.01  --bmc1_ucm_layered_model                none
% 2.72/1.01  --bmc1_ucm_max_lemma_size               10
% 2.72/1.01  
% 2.72/1.01  ------ AIG Options
% 2.72/1.01  
% 2.72/1.01  --aig_mode                              false
% 2.72/1.01  
% 2.72/1.01  ------ Instantiation Options
% 2.72/1.01  
% 2.72/1.01  --instantiation_flag                    true
% 2.72/1.01  --inst_sos_flag                         false
% 2.72/1.01  --inst_sos_phase                        true
% 2.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel_side                     num_symb
% 2.72/1.01  --inst_solver_per_active                1400
% 2.72/1.01  --inst_solver_calls_frac                1.
% 2.72/1.01  --inst_passive_queue_type               priority_queues
% 2.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/1.01  --inst_passive_queues_freq              [25;2]
% 2.72/1.01  --inst_dismatching                      true
% 2.72/1.01  --inst_eager_unprocessed_to_passive     true
% 2.72/1.01  --inst_prop_sim_given                   true
% 2.72/1.01  --inst_prop_sim_new                     false
% 2.72/1.01  --inst_subs_new                         false
% 2.72/1.01  --inst_eq_res_simp                      false
% 2.72/1.01  --inst_subs_given                       false
% 2.72/1.01  --inst_orphan_elimination               true
% 2.72/1.01  --inst_learning_loop_flag               true
% 2.72/1.01  --inst_learning_start                   3000
% 2.72/1.01  --inst_learning_factor                  2
% 2.72/1.01  --inst_start_prop_sim_after_learn       3
% 2.72/1.01  --inst_sel_renew                        solver
% 2.72/1.01  --inst_lit_activity_flag                true
% 2.72/1.01  --inst_restr_to_given                   false
% 2.72/1.01  --inst_activity_threshold               500
% 2.72/1.01  --inst_out_proof                        true
% 2.72/1.01  
% 2.72/1.01  ------ Resolution Options
% 2.72/1.01  
% 2.72/1.01  --resolution_flag                       true
% 2.72/1.01  --res_lit_sel                           adaptive
% 2.72/1.01  --res_lit_sel_side                      none
% 2.72/1.01  --res_ordering                          kbo
% 2.72/1.01  --res_to_prop_solver                    active
% 2.72/1.01  --res_prop_simpl_new                    false
% 2.72/1.01  --res_prop_simpl_given                  true
% 2.72/1.01  --res_passive_queue_type                priority_queues
% 2.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/1.01  --res_passive_queues_freq               [15;5]
% 2.72/1.01  --res_forward_subs                      full
% 2.72/1.01  --res_backward_subs                     full
% 2.72/1.01  --res_forward_subs_resolution           true
% 2.72/1.01  --res_backward_subs_resolution          true
% 2.72/1.01  --res_orphan_elimination                true
% 2.72/1.01  --res_time_limit                        2.
% 2.72/1.01  --res_out_proof                         true
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Options
% 2.72/1.01  
% 2.72/1.01  --superposition_flag                    true
% 2.72/1.01  --sup_passive_queue_type                priority_queues
% 2.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.72/1.01  --demod_completeness_check              fast
% 2.72/1.01  --demod_use_ground                      true
% 2.72/1.01  --sup_to_prop_solver                    passive
% 2.72/1.01  --sup_prop_simpl_new                    true
% 2.72/1.01  --sup_prop_simpl_given                  true
% 2.72/1.01  --sup_fun_splitting                     false
% 2.72/1.01  --sup_smt_interval                      50000
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Simplification Setup
% 2.72/1.01  
% 2.72/1.01  --sup_indices_passive                   []
% 2.72/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.01  --sup_full_bw                           [BwDemod]
% 2.72/1.01  --sup_immed_triv                        [TrivRules]
% 2.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.01  --sup_immed_bw_main                     []
% 2.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.01  
% 2.72/1.01  ------ Combination Options
% 2.72/1.01  
% 2.72/1.01  --comb_res_mult                         3
% 2.72/1.01  --comb_sup_mult                         2
% 2.72/1.01  --comb_inst_mult                        10
% 2.72/1.01  
% 2.72/1.01  ------ Debug Options
% 2.72/1.01  
% 2.72/1.01  --dbg_backtrace                         false
% 2.72/1.01  --dbg_dump_prop_clauses                 false
% 2.72/1.01  --dbg_dump_prop_clauses_file            -
% 2.72/1.01  --dbg_out_stat                          false
% 2.72/1.01  ------ Parsing...
% 2.72/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/1.01  ------ Proving...
% 2.72/1.01  ------ Problem Properties 
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  clauses                                 25
% 2.72/1.01  conjectures                             2
% 2.72/1.01  EPR                                     5
% 2.72/1.01  Horn                                    20
% 2.72/1.01  unary                                   5
% 2.72/1.01  binary                                  12
% 2.72/1.01  lits                                    59
% 2.72/1.01  lits eq                                 25
% 2.72/1.01  fd_pure                                 0
% 2.72/1.01  fd_pseudo                               0
% 2.72/1.01  fd_cond                                 0
% 2.72/1.01  fd_pseudo_cond                          5
% 2.72/1.01  AC symbols                              0
% 2.72/1.01  
% 2.72/1.01  ------ Schedule dynamic 5 is on 
% 2.72/1.01  
% 2.72/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  ------ 
% 2.72/1.01  Current options:
% 2.72/1.01  ------ 
% 2.72/1.01  
% 2.72/1.01  ------ Input Options
% 2.72/1.01  
% 2.72/1.01  --out_options                           all
% 2.72/1.01  --tptp_safe_out                         true
% 2.72/1.01  --problem_path                          ""
% 2.72/1.01  --include_path                          ""
% 2.72/1.01  --clausifier                            res/vclausify_rel
% 2.72/1.01  --clausifier_options                    --mode clausify
% 2.72/1.01  --stdin                                 false
% 2.72/1.01  --stats_out                             all
% 2.72/1.01  
% 2.72/1.01  ------ General Options
% 2.72/1.01  
% 2.72/1.01  --fof                                   false
% 2.72/1.01  --time_out_real                         305.
% 2.72/1.01  --time_out_virtual                      -1.
% 2.72/1.01  --symbol_type_check                     false
% 2.72/1.01  --clausify_out                          false
% 2.72/1.01  --sig_cnt_out                           false
% 2.72/1.01  --trig_cnt_out                          false
% 2.72/1.01  --trig_cnt_out_tolerance                1.
% 2.72/1.01  --trig_cnt_out_sk_spl                   false
% 2.72/1.01  --abstr_cl_out                          false
% 2.72/1.01  
% 2.72/1.01  ------ Global Options
% 2.72/1.01  
% 2.72/1.01  --schedule                              default
% 2.72/1.01  --add_important_lit                     false
% 2.72/1.01  --prop_solver_per_cl                    1000
% 2.72/1.01  --min_unsat_core                        false
% 2.72/1.01  --soft_assumptions                      false
% 2.72/1.01  --soft_lemma_size                       3
% 2.72/1.01  --prop_impl_unit_size                   0
% 2.72/1.01  --prop_impl_unit                        []
% 2.72/1.01  --share_sel_clauses                     true
% 2.72/1.01  --reset_solvers                         false
% 2.72/1.01  --bc_imp_inh                            [conj_cone]
% 2.72/1.01  --conj_cone_tolerance                   3.
% 2.72/1.01  --extra_neg_conj                        none
% 2.72/1.01  --large_theory_mode                     true
% 2.72/1.01  --prolific_symb_bound                   200
% 2.72/1.01  --lt_threshold                          2000
% 2.72/1.01  --clause_weak_htbl                      true
% 2.72/1.01  --gc_record_bc_elim                     false
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing Options
% 2.72/1.01  
% 2.72/1.01  --preprocessing_flag                    true
% 2.72/1.01  --time_out_prep_mult                    0.1
% 2.72/1.01  --splitting_mode                        input
% 2.72/1.01  --splitting_grd                         true
% 2.72/1.01  --splitting_cvd                         false
% 2.72/1.01  --splitting_cvd_svl                     false
% 2.72/1.01  --splitting_nvd                         32
% 2.72/1.01  --sub_typing                            true
% 2.72/1.01  --prep_gs_sim                           true
% 2.72/1.01  --prep_unflatten                        true
% 2.72/1.01  --prep_res_sim                          true
% 2.72/1.01  --prep_upred                            true
% 2.72/1.01  --prep_sem_filter                       exhaustive
% 2.72/1.01  --prep_sem_filter_out                   false
% 2.72/1.01  --pred_elim                             true
% 2.72/1.01  --res_sim_input                         true
% 2.72/1.01  --eq_ax_congr_red                       true
% 2.72/1.01  --pure_diseq_elim                       true
% 2.72/1.01  --brand_transform                       false
% 2.72/1.01  --non_eq_to_eq                          false
% 2.72/1.01  --prep_def_merge                        true
% 2.72/1.01  --prep_def_merge_prop_impl              false
% 2.72/1.01  --prep_def_merge_mbd                    true
% 2.72/1.01  --prep_def_merge_tr_red                 false
% 2.72/1.01  --prep_def_merge_tr_cl                  false
% 2.72/1.01  --smt_preprocessing                     true
% 2.72/1.01  --smt_ac_axioms                         fast
% 2.72/1.01  --preprocessed_out                      false
% 2.72/1.01  --preprocessed_stats                    false
% 2.72/1.01  
% 2.72/1.01  ------ Abstraction refinement Options
% 2.72/1.01  
% 2.72/1.01  --abstr_ref                             []
% 2.72/1.01  --abstr_ref_prep                        false
% 2.72/1.01  --abstr_ref_until_sat                   false
% 2.72/1.01  --abstr_ref_sig_restrict                funpre
% 2.72/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/1.01  --abstr_ref_under                       []
% 2.72/1.01  
% 2.72/1.01  ------ SAT Options
% 2.72/1.01  
% 2.72/1.01  --sat_mode                              false
% 2.72/1.01  --sat_fm_restart_options                ""
% 2.72/1.01  --sat_gr_def                            false
% 2.72/1.01  --sat_epr_types                         true
% 2.72/1.01  --sat_non_cyclic_types                  false
% 2.72/1.01  --sat_finite_models                     false
% 2.72/1.01  --sat_fm_lemmas                         false
% 2.72/1.01  --sat_fm_prep                           false
% 2.72/1.01  --sat_fm_uc_incr                        true
% 2.72/1.01  --sat_out_model                         small
% 2.72/1.01  --sat_out_clauses                       false
% 2.72/1.01  
% 2.72/1.01  ------ QBF Options
% 2.72/1.01  
% 2.72/1.01  --qbf_mode                              false
% 2.72/1.01  --qbf_elim_univ                         false
% 2.72/1.01  --qbf_dom_inst                          none
% 2.72/1.01  --qbf_dom_pre_inst                      false
% 2.72/1.01  --qbf_sk_in                             false
% 2.72/1.01  --qbf_pred_elim                         true
% 2.72/1.01  --qbf_split                             512
% 2.72/1.01  
% 2.72/1.01  ------ BMC1 Options
% 2.72/1.01  
% 2.72/1.01  --bmc1_incremental                      false
% 2.72/1.01  --bmc1_axioms                           reachable_all
% 2.72/1.01  --bmc1_min_bound                        0
% 2.72/1.01  --bmc1_max_bound                        -1
% 2.72/1.01  --bmc1_max_bound_default                -1
% 2.72/1.01  --bmc1_symbol_reachability              true
% 2.72/1.01  --bmc1_property_lemmas                  false
% 2.72/1.01  --bmc1_k_induction                      false
% 2.72/1.01  --bmc1_non_equiv_states                 false
% 2.72/1.01  --bmc1_deadlock                         false
% 2.72/1.01  --bmc1_ucm                              false
% 2.72/1.01  --bmc1_add_unsat_core                   none
% 2.72/1.01  --bmc1_unsat_core_children              false
% 2.72/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/1.01  --bmc1_out_stat                         full
% 2.72/1.01  --bmc1_ground_init                      false
% 2.72/1.01  --bmc1_pre_inst_next_state              false
% 2.72/1.01  --bmc1_pre_inst_state                   false
% 2.72/1.01  --bmc1_pre_inst_reach_state             false
% 2.72/1.01  --bmc1_out_unsat_core                   false
% 2.72/1.01  --bmc1_aig_witness_out                  false
% 2.72/1.01  --bmc1_verbose                          false
% 2.72/1.01  --bmc1_dump_clauses_tptp                false
% 2.72/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.72/1.01  --bmc1_dump_file                        -
% 2.72/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.72/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.72/1.01  --bmc1_ucm_extend_mode                  1
% 2.72/1.01  --bmc1_ucm_init_mode                    2
% 2.72/1.01  --bmc1_ucm_cone_mode                    none
% 2.72/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.72/1.01  --bmc1_ucm_relax_model                  4
% 2.72/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.72/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/1.01  --bmc1_ucm_layered_model                none
% 2.72/1.01  --bmc1_ucm_max_lemma_size               10
% 2.72/1.01  
% 2.72/1.01  ------ AIG Options
% 2.72/1.01  
% 2.72/1.01  --aig_mode                              false
% 2.72/1.01  
% 2.72/1.01  ------ Instantiation Options
% 2.72/1.01  
% 2.72/1.01  --instantiation_flag                    true
% 2.72/1.01  --inst_sos_flag                         false
% 2.72/1.01  --inst_sos_phase                        true
% 2.72/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/1.01  --inst_lit_sel_side                     none
% 2.72/1.01  --inst_solver_per_active                1400
% 2.72/1.01  --inst_solver_calls_frac                1.
% 2.72/1.01  --inst_passive_queue_type               priority_queues
% 2.72/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/1.01  --inst_passive_queues_freq              [25;2]
% 2.72/1.01  --inst_dismatching                      true
% 2.72/1.01  --inst_eager_unprocessed_to_passive     true
% 2.72/1.01  --inst_prop_sim_given                   true
% 2.72/1.01  --inst_prop_sim_new                     false
% 2.72/1.01  --inst_subs_new                         false
% 2.72/1.01  --inst_eq_res_simp                      false
% 2.72/1.01  --inst_subs_given                       false
% 2.72/1.01  --inst_orphan_elimination               true
% 2.72/1.01  --inst_learning_loop_flag               true
% 2.72/1.01  --inst_learning_start                   3000
% 2.72/1.01  --inst_learning_factor                  2
% 2.72/1.01  --inst_start_prop_sim_after_learn       3
% 2.72/1.01  --inst_sel_renew                        solver
% 2.72/1.01  --inst_lit_activity_flag                true
% 2.72/1.01  --inst_restr_to_given                   false
% 2.72/1.01  --inst_activity_threshold               500
% 2.72/1.01  --inst_out_proof                        true
% 2.72/1.01  
% 2.72/1.01  ------ Resolution Options
% 2.72/1.01  
% 2.72/1.01  --resolution_flag                       false
% 2.72/1.01  --res_lit_sel                           adaptive
% 2.72/1.01  --res_lit_sel_side                      none
% 2.72/1.01  --res_ordering                          kbo
% 2.72/1.01  --res_to_prop_solver                    active
% 2.72/1.01  --res_prop_simpl_new                    false
% 2.72/1.01  --res_prop_simpl_given                  true
% 2.72/1.01  --res_passive_queue_type                priority_queues
% 2.72/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/1.01  --res_passive_queues_freq               [15;5]
% 2.72/1.01  --res_forward_subs                      full
% 2.72/1.01  --res_backward_subs                     full
% 2.72/1.01  --res_forward_subs_resolution           true
% 2.72/1.01  --res_backward_subs_resolution          true
% 2.72/1.01  --res_orphan_elimination                true
% 2.72/1.01  --res_time_limit                        2.
% 2.72/1.01  --res_out_proof                         true
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Options
% 2.72/1.01  
% 2.72/1.01  --superposition_flag                    true
% 2.72/1.01  --sup_passive_queue_type                priority_queues
% 2.72/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.72/1.01  --demod_completeness_check              fast
% 2.72/1.01  --demod_use_ground                      true
% 2.72/1.01  --sup_to_prop_solver                    passive
% 2.72/1.01  --sup_prop_simpl_new                    true
% 2.72/1.01  --sup_prop_simpl_given                  true
% 2.72/1.01  --sup_fun_splitting                     false
% 2.72/1.01  --sup_smt_interval                      50000
% 2.72/1.01  
% 2.72/1.01  ------ Superposition Simplification Setup
% 2.72/1.01  
% 2.72/1.01  --sup_indices_passive                   []
% 2.72/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.01  --sup_full_bw                           [BwDemod]
% 2.72/1.01  --sup_immed_triv                        [TrivRules]
% 2.72/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.01  --sup_immed_bw_main                     []
% 2.72/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.01  
% 2.72/1.01  ------ Combination Options
% 2.72/1.01  
% 2.72/1.01  --comb_res_mult                         3
% 2.72/1.01  --comb_sup_mult                         2
% 2.72/1.01  --comb_inst_mult                        10
% 2.72/1.01  
% 2.72/1.01  ------ Debug Options
% 2.72/1.01  
% 2.72/1.01  --dbg_backtrace                         false
% 2.72/1.01  --dbg_dump_prop_clauses                 false
% 2.72/1.01  --dbg_dump_prop_clauses_file            -
% 2.72/1.01  --dbg_out_stat                          false
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  ------ Proving...
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  % SZS status Theorem for theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  fof(f5,axiom,(
% 2.72/1.01    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f14,plain,(
% 2.72/1.01    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.72/1.01    inference(ennf_transformation,[],[f5])).
% 2.72/1.01  
% 2.72/1.01  fof(f26,plain,(
% 2.72/1.01    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 2.72/1.01    introduced(choice_axiom,[])).
% 2.72/1.01  
% 2.72/1.01  fof(f27,plain,(
% 2.72/1.01    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f26])).
% 2.72/1.01  
% 2.72/1.01  fof(f44,plain,(
% 2.72/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.72/1.01    inference(cnf_transformation,[],[f27])).
% 2.72/1.01  
% 2.72/1.01  fof(f1,axiom,(
% 2.72/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f40,plain,(
% 2.72/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f1])).
% 2.72/1.01  
% 2.72/1.01  fof(f2,axiom,(
% 2.72/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f41,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f2])).
% 2.72/1.01  
% 2.72/1.01  fof(f3,axiom,(
% 2.72/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f42,plain,(
% 2.72/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f3])).
% 2.72/1.01  
% 2.72/1.01  fof(f4,axiom,(
% 2.72/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f43,plain,(
% 2.72/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f4])).
% 2.72/1.01  
% 2.72/1.01  fof(f71,plain,(
% 2.72/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f42,f43])).
% 2.72/1.01  
% 2.72/1.01  fof(f72,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f41,f71])).
% 2.72/1.01  
% 2.72/1.01  fof(f73,plain,(
% 2.72/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f40,f72])).
% 2.72/1.01  
% 2.72/1.01  fof(f75,plain,(
% 2.72/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 2.72/1.01    inference(definition_unfolding,[],[f44,f73])).
% 2.72/1.01  
% 2.72/1.01  fof(f12,conjecture,(
% 2.72/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f13,negated_conjecture,(
% 2.72/1.01    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.72/1.01    inference(negated_conjecture,[],[f12])).
% 2.72/1.01  
% 2.72/1.01  fof(f22,plain,(
% 2.72/1.01    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.72/1.01    inference(ennf_transformation,[],[f13])).
% 2.72/1.01  
% 2.72/1.01  fof(f23,plain,(
% 2.72/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.72/1.01    inference(flattening,[],[f22])).
% 2.72/1.01  
% 2.72/1.01  fof(f38,plain,(
% 2.72/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK4,sK3)) != k2_relat_1(sK4) & k1_tarski(sK3) = k1_relat_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 2.72/1.01    introduced(choice_axiom,[])).
% 2.72/1.01  
% 2.72/1.01  fof(f39,plain,(
% 2.72/1.01    k1_tarski(k1_funct_1(sK4,sK3)) != k2_relat_1(sK4) & k1_tarski(sK3) = k1_relat_1(sK4) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 2.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f38])).
% 2.72/1.01  
% 2.72/1.01  fof(f69,plain,(
% 2.72/1.01    k1_tarski(sK3) = k1_relat_1(sK4)),
% 2.72/1.01    inference(cnf_transformation,[],[f39])).
% 2.72/1.01  
% 2.72/1.01  fof(f80,plain,(
% 2.72/1.01    k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK4)),
% 2.72/1.01    inference(definition_unfolding,[],[f69,f73])).
% 2.72/1.01  
% 2.72/1.01  fof(f7,axiom,(
% 2.72/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f16,plain,(
% 2.72/1.01    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.72/1.01    inference(ennf_transformation,[],[f7])).
% 2.72/1.01  
% 2.72/1.01  fof(f58,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f16])).
% 2.72/1.01  
% 2.72/1.01  fof(f78,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.72/1.01    inference(definition_unfolding,[],[f58,f73])).
% 2.72/1.01  
% 2.72/1.01  fof(f67,plain,(
% 2.72/1.01    v1_relat_1(sK4)),
% 2.72/1.01    inference(cnf_transformation,[],[f39])).
% 2.72/1.01  
% 2.72/1.01  fof(f8,axiom,(
% 2.72/1.01    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f17,plain,(
% 2.72/1.01    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.72/1.01    inference(ennf_transformation,[],[f8])).
% 2.72/1.01  
% 2.72/1.01  fof(f59,plain,(
% 2.72/1.01    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f17])).
% 2.72/1.01  
% 2.72/1.01  fof(f9,axiom,(
% 2.72/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f18,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 2.72/1.01    inference(ennf_transformation,[],[f9])).
% 2.72/1.01  
% 2.72/1.01  fof(f34,plain,(
% 2.72/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 2.72/1.01    inference(nnf_transformation,[],[f18])).
% 2.72/1.01  
% 2.72/1.01  fof(f61,plain,(
% 2.72/1.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f34])).
% 2.72/1.01  
% 2.72/1.01  fof(f11,axiom,(
% 2.72/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f20,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.72/1.01    inference(ennf_transformation,[],[f11])).
% 2.72/1.01  
% 2.72/1.01  fof(f21,plain,(
% 2.72/1.01    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.72/1.01    inference(flattening,[],[f20])).
% 2.72/1.01  
% 2.72/1.01  fof(f36,plain,(
% 2.72/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.72/1.01    inference(nnf_transformation,[],[f21])).
% 2.72/1.01  
% 2.72/1.01  fof(f37,plain,(
% 2.72/1.01    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.72/1.01    inference(flattening,[],[f36])).
% 2.72/1.01  
% 2.72/1.01  fof(f65,plain,(
% 2.72/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f37])).
% 2.72/1.01  
% 2.72/1.01  fof(f68,plain,(
% 2.72/1.01    v1_funct_1(sK4)),
% 2.72/1.01    inference(cnf_transformation,[],[f39])).
% 2.72/1.01  
% 2.72/1.01  fof(f24,plain,(
% 2.72/1.01    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 2.72/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.72/1.01  
% 2.72/1.01  fof(f28,plain,(
% 2.72/1.01    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 2.72/1.01    inference(nnf_transformation,[],[f24])).
% 2.72/1.01  
% 2.72/1.01  fof(f29,plain,(
% 2.72/1.01    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 2.72/1.01    inference(flattening,[],[f28])).
% 2.72/1.01  
% 2.72/1.01  fof(f30,plain,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.72/1.01    inference(rectify,[],[f29])).
% 2.72/1.01  
% 2.72/1.01  fof(f31,plain,(
% 2.72/1.01    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK2(X0,X1,X2,X3,X4) != X0 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X0 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4))))),
% 2.72/1.01    introduced(choice_axiom,[])).
% 2.72/1.01  
% 2.72/1.01  fof(f32,plain,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK2(X0,X1,X2,X3,X4) != X0 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X0 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.72/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 2.72/1.01  
% 2.72/1.01  fof(f50,plain,(
% 2.72/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X0 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f32])).
% 2.72/1.01  
% 2.72/1.01  fof(f81,plain,(
% 2.72/1.01    ( ! [X6,X4,X2,X3,X1] : (r2_hidden(X6,X4) | ~sP0(X6,X1,X2,X3,X4)) )),
% 2.72/1.01    inference(equality_resolution,[],[f50])).
% 2.72/1.01  
% 2.72/1.01  fof(f6,axiom,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f15,plain,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 2.72/1.01    inference(ennf_transformation,[],[f6])).
% 2.72/1.01  
% 2.72/1.01  fof(f25,plain,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 2.72/1.01    inference(definition_folding,[],[f15,f24])).
% 2.72/1.01  
% 2.72/1.01  fof(f33,plain,(
% 2.72/1.01    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 2.72/1.01    inference(nnf_transformation,[],[f25])).
% 2.72/1.01  
% 2.72/1.01  fof(f56,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 2.72/1.01    inference(cnf_transformation,[],[f33])).
% 2.72/1.01  
% 2.72/1.01  fof(f77,plain,(
% 2.72/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k3_enumset1(X0,X0,X1,X2,X3) != X4) )),
% 2.72/1.01    inference(definition_unfolding,[],[f56,f43])).
% 2.72/1.01  
% 2.72/1.01  fof(f85,plain,(
% 2.72/1.01    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k3_enumset1(X0,X0,X1,X2,X3))) )),
% 2.72/1.01    inference(equality_resolution,[],[f77])).
% 2.72/1.01  
% 2.72/1.01  fof(f10,axiom,(
% 2.72/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.72/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/1.01  
% 2.72/1.01  fof(f19,plain,(
% 2.72/1.01    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.72/1.01    inference(ennf_transformation,[],[f10])).
% 2.72/1.01  
% 2.72/1.01  fof(f35,plain,(
% 2.72/1.01    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.72/1.01    inference(nnf_transformation,[],[f19])).
% 2.72/1.01  
% 2.72/1.01  fof(f62,plain,(
% 2.72/1.01    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.72/1.01    inference(cnf_transformation,[],[f35])).
% 2.72/1.01  
% 2.72/1.01  fof(f70,plain,(
% 2.72/1.01    k1_tarski(k1_funct_1(sK4,sK3)) != k2_relat_1(sK4)),
% 2.72/1.01    inference(cnf_transformation,[],[f39])).
% 2.72/1.01  
% 2.72/1.01  fof(f79,plain,(
% 2.72/1.01    k3_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k2_relat_1(sK4)),
% 2.72/1.01    inference(definition_unfolding,[],[f70,f73])).
% 2.72/1.01  
% 2.72/1.01  fof(f45,plain,(
% 2.72/1.01    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.72/1.01    inference(cnf_transformation,[],[f27])).
% 2.72/1.01  
% 2.72/1.01  fof(f74,plain,(
% 2.72/1.01    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 2.72/1.01    inference(definition_unfolding,[],[f45,f73])).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1,plain,
% 2.72/1.01      ( r2_hidden(sK1(X0,X1),X0)
% 2.72/1.01      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.72/1.01      | k1_xboole_0 = X0 ),
% 2.72/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2471,plain,
% 2.72/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.72/1.01      | k1_xboole_0 = X1
% 2.72/1.01      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_24,negated_conjecture,
% 2.72/1.01      ( k3_enumset1(sK3,sK3,sK3,sK3,sK3) = k1_relat_1(sK4) ),
% 2.72/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_14,plain,
% 2.72/1.01      ( ~ v1_relat_1(X0)
% 2.72/1.01      | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.72/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_26,negated_conjecture,
% 2.72/1.01      ( v1_relat_1(sK4) ),
% 2.72/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_340,plain,
% 2.72/1.01      ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.72/1.01      | sK4 != X0 ),
% 2.72/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_341,plain,
% 2.72/1.01      ( k9_relat_1(sK4,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 2.72/1.01      inference(unflattening,[status(thm)],[c_340]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2661,plain,
% 2.72/1.01      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK3) ),
% 2.72/1.01      inference(superposition,[status(thm)],[c_24,c_341]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_15,plain,
% 2.72/1.01      ( ~ v1_relat_1(X0)
% 2.72/1.01      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.72/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_335,plain,
% 2.72/1.01      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK4 != X0 ),
% 2.72/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_336,plain,
% 2.72/1.01      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.72/1.01      inference(unflattening,[status(thm)],[c_335]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2662,plain,
% 2.72/1.01      ( k11_relat_1(sK4,sK3) = k2_relat_1(sK4) ),
% 2.72/1.01      inference(light_normalisation,[status(thm)],[c_2661,c_336]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_16,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.72/1.01      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.72/1.01      | ~ v1_relat_1(X1) ),
% 2.72/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_382,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k11_relat_1(X1,X2))
% 2.72/1.01      | r2_hidden(k4_tarski(X2,X0),X1)
% 2.72/1.01      | sK4 != X1 ),
% 2.72/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_383,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
% 2.72/1.01      | r2_hidden(k4_tarski(X1,X0),sK4) ),
% 2.72/1.01      inference(unflattening,[status(thm)],[c_382]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1160,plain,
% 2.72/1.01      ( r2_hidden(k4_tarski(X1,X0),sK4)
% 2.72/1.01      | ~ r2_hidden(X0,k11_relat_1(sK4,X1)) ),
% 2.72/1.01      inference(prop_impl,[status(thm)],[c_383]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1161,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k11_relat_1(sK4,X1))
% 2.72/1.01      | r2_hidden(k4_tarski(X1,X0),sK4) ),
% 2.72/1.01      inference(renaming,[status(thm)],[c_1160]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2452,plain,
% 2.72/1.01      ( r2_hidden(X0,k11_relat_1(sK4,X1)) != iProver_top
% 2.72/1.01      | r2_hidden(k4_tarski(X1,X0),sK4) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2893,plain,
% 2.72/1.01      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.72/1.01      | r2_hidden(k4_tarski(sK3,X0),sK4) = iProver_top ),
% 2.72/1.01      inference(superposition,[status(thm)],[c_2662,c_2452]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_21,plain,
% 2.72/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.72/1.01      | ~ v1_funct_1(X2)
% 2.72/1.01      | ~ v1_relat_1(X2)
% 2.72/1.01      | k1_funct_1(X2,X0) = X1 ),
% 2.72/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_25,negated_conjecture,
% 2.72/1.01      ( v1_funct_1(sK4) ),
% 2.72/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_272,plain,
% 2.72/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 2.72/1.01      | ~ v1_relat_1(X2)
% 2.72/1.01      | k1_funct_1(X2,X0) = X1
% 2.72/1.01      | sK4 != X2 ),
% 2.72/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_273,plain,
% 2.72/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 2.72/1.01      | ~ v1_relat_1(sK4)
% 2.72/1.01      | k1_funct_1(sK4,X0) = X1 ),
% 2.72/1.01      inference(unflattening,[status(thm)],[c_272]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_277,plain,
% 2.72/1.01      ( ~ r2_hidden(k4_tarski(X0,X1),sK4) | k1_funct_1(sK4,X0) = X1 ),
% 2.72/1.01      inference(global_propositional_subsumption,
% 2.72/1.01                [status(thm)],
% 2.72/1.01                [c_273,c_26]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2458,plain,
% 2.72/1.01      ( k1_funct_1(sK4,X0) = X1
% 2.72/1.01      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3126,plain,
% 2.72/1.01      ( k1_funct_1(sK4,sK3) = X0
% 2.72/1.01      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.72/1.01      inference(superposition,[status(thm)],[c_2893,c_2458]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3651,plain,
% 2.72/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK4)
% 2.72/1.01      | sK1(k2_relat_1(sK4),X0) = k1_funct_1(sK4,sK3)
% 2.72/1.01      | k2_relat_1(sK4) = k1_xboole_0 ),
% 2.72/1.01      inference(superposition,[status(thm)],[c_2471,c_3126]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_7,plain,
% 2.72/1.01      ( ~ sP0(X0,X1,X2,X3,X4) | r2_hidden(X0,X4) ),
% 2.72/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2785,plain,
% 2.72/1.01      ( ~ sP0(X0,X1,X2,X3,k1_relat_1(sK4))
% 2.72/1.01      | r2_hidden(X0,k1_relat_1(sK4)) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2786,plain,
% 2.72/1.01      ( sP0(X0,X1,X2,X3,k1_relat_1(sK4)) != iProver_top
% 2.72/1.01      | r2_hidden(X0,k1_relat_1(sK4)) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_2785]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2788,plain,
% 2.72/1.01      ( sP0(sK3,sK3,sK3,sK3,k1_relat_1(sK4)) != iProver_top
% 2.72/1.01      | r2_hidden(sK3,k1_relat_1(sK4)) = iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2786]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_13,plain,
% 2.72/1.01      ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) ),
% 2.72/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2459,plain,
% 2.72/1.01      ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) = iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2943,plain,
% 2.72/1.01      ( sP0(sK3,sK3,sK3,sK3,k1_relat_1(sK4)) = iProver_top ),
% 2.72/1.01      inference(superposition,[status(thm)],[c_24,c_2459]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_19,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/1.01      | ~ v1_relat_1(X1)
% 2.72/1.01      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 2.72/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_346,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/1.01      | k11_relat_1(X1,X0) != k1_xboole_0
% 2.72/1.01      | sK4 != X1 ),
% 2.72/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_347,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.72/1.01      | k11_relat_1(sK4,X0) != k1_xboole_0 ),
% 2.72/1.01      inference(unflattening,[status(thm)],[c_346]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1156,plain,
% 2.72/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.72/1.01      | k11_relat_1(sK4,X0) != k1_xboole_0 ),
% 2.72/1.01      inference(prop_impl,[status(thm)],[c_347]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2455,plain,
% 2.72/1.01      ( k11_relat_1(sK4,X0) != k1_xboole_0
% 2.72/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3362,plain,
% 2.72/1.01      ( k2_relat_1(sK4) != k1_xboole_0
% 2.72/1.01      | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
% 2.72/1.01      inference(superposition,[status(thm)],[c_2662,c_2455]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3847,plain,
% 2.72/1.01      ( sK1(k2_relat_1(sK4),X0) = k1_funct_1(sK4,sK3)
% 2.72/1.01      | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK4) ),
% 2.72/1.01      inference(global_propositional_subsumption,
% 2.72/1.01                [status(thm)],
% 2.72/1.01                [c_3651,c_2788,c_2943,c_3362]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3848,plain,
% 2.72/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK4)
% 2.72/1.01      | sK1(k2_relat_1(sK4),X0) = k1_funct_1(sK4,sK3) ),
% 2.72/1.01      inference(renaming,[status(thm)],[c_3847]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_23,negated_conjecture,
% 2.72/1.01      ( k3_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) != k2_relat_1(sK4) ),
% 2.72/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_3856,plain,
% 2.72/1.01      ( sK1(k2_relat_1(sK4),k1_funct_1(sK4,sK3)) = k1_funct_1(sK4,sK3) ),
% 2.72/1.01      inference(superposition,[status(thm)],[c_3848,c_23]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_1946,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2646,plain,
% 2.72/1.01      ( k11_relat_1(sK4,X0) != X1
% 2.72/1.01      | k11_relat_1(sK4,X0) = k1_xboole_0
% 2.72/1.01      | k1_xboole_0 != X1 ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_1946]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2934,plain,
% 2.72/1.01      ( k11_relat_1(sK4,X0) != k2_relat_1(sK4)
% 2.72/1.01      | k11_relat_1(sK4,X0) = k1_xboole_0
% 2.72/1.01      | k1_xboole_0 != k2_relat_1(sK4) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2646]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2935,plain,
% 2.72/1.01      ( k11_relat_1(sK4,sK3) != k2_relat_1(sK4)
% 2.72/1.01      | k11_relat_1(sK4,sK3) = k1_xboole_0
% 2.72/1.01      | k1_xboole_0 != k2_relat_1(sK4) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_2934]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_0,plain,
% 2.72/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.72/1.01      | sK1(X1,X0) != X0
% 2.72/1.01      | k1_xboole_0 = X1 ),
% 2.72/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_2663,plain,
% 2.72/1.01      ( k3_enumset1(k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3),k1_funct_1(sK4,sK3)) = k2_relat_1(sK4)
% 2.72/1.01      | sK1(k2_relat_1(sK4),k1_funct_1(sK4,sK3)) != k1_funct_1(sK4,sK3)
% 2.72/1.01      | k1_xboole_0 = k2_relat_1(sK4) ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_348,plain,
% 2.72/1.01      ( k11_relat_1(sK4,X0) != k1_xboole_0
% 2.72/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.72/1.01      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(c_350,plain,
% 2.72/1.01      ( k11_relat_1(sK4,sK3) != k1_xboole_0
% 2.72/1.01      | r2_hidden(sK3,k1_relat_1(sK4)) != iProver_top ),
% 2.72/1.01      inference(instantiation,[status(thm)],[c_348]) ).
% 2.72/1.01  
% 2.72/1.01  cnf(contradiction,plain,
% 2.72/1.01      ( $false ),
% 2.72/1.01      inference(minisat,
% 2.72/1.01                [status(thm)],
% 2.72/1.01                [c_3856,c_2943,c_2935,c_2788,c_2663,c_2662,c_350,c_23]) ).
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/1.01  
% 2.72/1.01  ------                               Statistics
% 2.72/1.01  
% 2.72/1.01  ------ General
% 2.72/1.01  
% 2.72/1.01  abstr_ref_over_cycles:                  0
% 2.72/1.01  abstr_ref_under_cycles:                 0
% 2.72/1.01  gc_basic_clause_elim:                   0
% 2.72/1.01  forced_gc_time:                         0
% 2.72/1.01  parsing_time:                           0.011
% 2.72/1.01  unif_index_cands_time:                  0.
% 2.72/1.01  unif_index_add_time:                    0.
% 2.72/1.01  orderings_time:                         0.
% 2.72/1.01  out_proof_time:                         0.012
% 2.72/1.01  total_time:                             0.144
% 2.72/1.01  num_of_symbols:                         47
% 2.72/1.01  num_of_terms:                           2421
% 2.72/1.01  
% 2.72/1.01  ------ Preprocessing
% 2.72/1.01  
% 2.72/1.01  num_of_splits:                          0
% 2.72/1.01  num_of_split_atoms:                     0
% 2.72/1.01  num_of_reused_defs:                     0
% 2.72/1.01  num_eq_ax_congr_red:                    41
% 2.72/1.01  num_of_sem_filtered_clauses:            1
% 2.72/1.01  num_of_subtypes:                        0
% 2.72/1.01  monotx_restored_types:                  0
% 2.72/1.01  sat_num_of_epr_types:                   0
% 2.72/1.01  sat_num_of_non_cyclic_types:            0
% 2.72/1.01  sat_guarded_non_collapsed_types:        0
% 2.72/1.01  num_pure_diseq_elim:                    0
% 2.72/1.01  simp_replaced_by:                       0
% 2.72/1.01  res_preprocessed:                       125
% 2.72/1.01  prep_upred:                             0
% 2.72/1.01  prep_unflattend:                        69
% 2.72/1.01  smt_new_axioms:                         0
% 2.72/1.01  pred_elim_cands:                        2
% 2.72/1.01  pred_elim:                              2
% 2.72/1.01  pred_elim_cl:                           2
% 2.72/1.01  pred_elim_cycles:                       4
% 2.72/1.01  merged_defs:                            12
% 2.72/1.01  merged_defs_ncl:                        0
% 2.72/1.01  bin_hyper_res:                          12
% 2.72/1.01  prep_cycles:                            4
% 2.72/1.01  pred_elim_time:                         0.02
% 2.72/1.01  splitting_time:                         0.
% 2.72/1.01  sem_filter_time:                        0.
% 2.72/1.01  monotx_time:                            0.
% 2.72/1.01  subtype_inf_time:                       0.
% 2.72/1.01  
% 2.72/1.01  ------ Problem properties
% 2.72/1.01  
% 2.72/1.01  clauses:                                25
% 2.72/1.01  conjectures:                            2
% 2.72/1.01  epr:                                    5
% 2.72/1.01  horn:                                   20
% 2.72/1.01  ground:                                 3
% 2.72/1.01  unary:                                  5
% 2.72/1.01  binary:                                 12
% 2.72/1.01  lits:                                   59
% 2.72/1.01  lits_eq:                                25
% 2.72/1.01  fd_pure:                                0
% 2.72/1.01  fd_pseudo:                              0
% 2.72/1.01  fd_cond:                                0
% 2.72/1.01  fd_pseudo_cond:                         5
% 2.72/1.01  ac_symbols:                             0
% 2.72/1.01  
% 2.72/1.01  ------ Propositional Solver
% 2.72/1.01  
% 2.72/1.01  prop_solver_calls:                      25
% 2.72/1.01  prop_fast_solver_calls:                 983
% 2.72/1.01  smt_solver_calls:                       0
% 2.72/1.01  smt_fast_solver_calls:                  0
% 2.72/1.01  prop_num_of_clauses:                    878
% 2.72/1.01  prop_preprocess_simplified:             4932
% 2.72/1.01  prop_fo_subsumed:                       7
% 2.72/1.01  prop_solver_time:                       0.
% 2.72/1.01  smt_solver_time:                        0.
% 2.72/1.01  smt_fast_solver_time:                   0.
% 2.72/1.01  prop_fast_solver_time:                  0.
% 2.72/1.01  prop_unsat_core_time:                   0.
% 2.72/1.01  
% 2.72/1.01  ------ QBF
% 2.72/1.01  
% 2.72/1.01  qbf_q_res:                              0
% 2.72/1.01  qbf_num_tautologies:                    0
% 2.72/1.01  qbf_prep_cycles:                        0
% 2.72/1.01  
% 2.72/1.01  ------ BMC1
% 2.72/1.01  
% 2.72/1.01  bmc1_current_bound:                     -1
% 2.72/1.01  bmc1_last_solved_bound:                 -1
% 2.72/1.01  bmc1_unsat_core_size:                   -1
% 2.72/1.01  bmc1_unsat_core_parents_size:           -1
% 2.72/1.01  bmc1_merge_next_fun:                    0
% 2.72/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.72/1.01  
% 2.72/1.01  ------ Instantiation
% 2.72/1.01  
% 2.72/1.01  inst_num_of_clauses:                    216
% 2.72/1.01  inst_num_in_passive:                    66
% 2.72/1.01  inst_num_in_active:                     98
% 2.72/1.01  inst_num_in_unprocessed:                52
% 2.72/1.01  inst_num_of_loops:                      150
% 2.72/1.01  inst_num_of_learning_restarts:          0
% 2.72/1.01  inst_num_moves_active_passive:          51
% 2.72/1.01  inst_lit_activity:                      0
% 2.72/1.01  inst_lit_activity_moves:                0
% 2.72/1.01  inst_num_tautologies:                   0
% 2.72/1.01  inst_num_prop_implied:                  0
% 2.72/1.01  inst_num_existing_simplified:           0
% 2.72/1.01  inst_num_eq_res_simplified:             0
% 2.72/1.01  inst_num_child_elim:                    0
% 2.72/1.01  inst_num_of_dismatching_blockings:      38
% 2.72/1.01  inst_num_of_non_proper_insts:           150
% 2.72/1.01  inst_num_of_duplicates:                 0
% 2.72/1.01  inst_inst_num_from_inst_to_res:         0
% 2.72/1.01  inst_dismatching_checking_time:         0.
% 2.72/1.01  
% 2.72/1.01  ------ Resolution
% 2.72/1.01  
% 2.72/1.01  res_num_of_clauses:                     0
% 2.72/1.01  res_num_in_passive:                     0
% 2.72/1.01  res_num_in_active:                      0
% 2.72/1.01  res_num_of_loops:                       129
% 2.72/1.01  res_forward_subset_subsumed:            7
% 2.72/1.01  res_backward_subset_subsumed:           2
% 2.72/1.01  res_forward_subsumed:                   0
% 2.72/1.01  res_backward_subsumed:                  0
% 2.72/1.01  res_forward_subsumption_resolution:     0
% 2.72/1.01  res_backward_subsumption_resolution:    0
% 2.72/1.01  res_clause_to_clause_subsumption:       673
% 2.72/1.01  res_orphan_elimination:                 0
% 2.72/1.01  res_tautology_del:                      28
% 2.72/1.01  res_num_eq_res_simplified:              0
% 2.72/1.01  res_num_sel_changes:                    0
% 2.72/1.01  res_moves_from_active_to_pass:          0
% 2.72/1.01  
% 2.72/1.01  ------ Superposition
% 2.72/1.01  
% 2.72/1.01  sup_time_total:                         0.
% 2.72/1.01  sup_time_generating:                    0.
% 2.72/1.01  sup_time_sim_full:                      0.
% 2.72/1.01  sup_time_sim_immed:                     0.
% 2.72/1.01  
% 2.72/1.01  sup_num_of_clauses:                     45
% 2.72/1.01  sup_num_in_active:                      29
% 2.72/1.01  sup_num_in_passive:                     16
% 2.72/1.01  sup_num_of_loops:                       28
% 2.72/1.01  sup_fw_superposition:                   19
% 2.72/1.01  sup_bw_superposition:                   13
% 2.72/1.01  sup_immediate_simplified:               2
% 2.72/1.01  sup_given_eliminated:                   0
% 2.72/1.01  comparisons_done:                       0
% 2.72/1.01  comparisons_avoided:                    3
% 2.72/1.01  
% 2.72/1.01  ------ Simplifications
% 2.72/1.01  
% 2.72/1.01  
% 2.72/1.01  sim_fw_subset_subsumed:                 0
% 2.72/1.01  sim_bw_subset_subsumed:                 0
% 2.72/1.01  sim_fw_subsumed:                        0
% 2.72/1.01  sim_bw_subsumed:                        0
% 2.72/1.01  sim_fw_subsumption_res:                 0
% 2.72/1.01  sim_bw_subsumption_res:                 0
% 2.72/1.01  sim_tautology_del:                      2
% 2.72/1.01  sim_eq_tautology_del:                   3
% 2.72/1.01  sim_eq_res_simp:                        0
% 2.72/1.01  sim_fw_demodulated:                     0
% 2.72/1.01  sim_bw_demodulated:                     0
% 2.72/1.01  sim_light_normalised:                   2
% 2.72/1.01  sim_joinable_taut:                      0
% 2.72/1.01  sim_joinable_simp:                      0
% 2.72/1.01  sim_ac_normalised:                      0
% 2.72/1.01  sim_smt_subsumption:                    0
% 2.72/1.01  
%------------------------------------------------------------------------------
