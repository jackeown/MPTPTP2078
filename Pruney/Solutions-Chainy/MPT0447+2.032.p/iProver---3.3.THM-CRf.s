%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:14 EST 2020

% Result     : Theorem 43.63s
% Output     : CNFRefutation 43.63s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 745 expanded)
%              Number of clauses        :   59 ( 114 expanded)
%              Number of leaves         :   22 ( 214 expanded)
%              Depth                    :   22
%              Number of atoms          :  381 (1588 expanded)
%              Number of equality atoms :  195 ( 847 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK4))
        & r1_tarski(X0,sK4)
        & v1_relat_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK3),k3_relat_1(X1))
          & r1_tarski(sK3,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4))
    & r1_tarski(sK3,sK4)
    & v1_relat_1(sK4)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f42,f41])).

fof(f76,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f82])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f83])).

fof(f90,plain,(
    ! [X0] :
      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f72,f85])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f47,f83,f83])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f85])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f85])).

fof(f77,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f70,f83])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f84])).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f30,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f22,f31,f30])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f68])).

fof(f37,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f38])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f67])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ~ r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1355,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1360,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3168,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k2_relat_1(sK4))) = k3_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1355,c_1360])).

cnf(c_3,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1378,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2558,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1378])).

cnf(c_3472,plain,
    ( r1_tarski(k2_relat_1(sK4),k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_2558])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1377,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1356,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1359,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1379,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3080,plain,
    ( k1_setfam_1(k6_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1379])).

cnf(c_5498,plain,
    ( k1_setfam_1(k6_enumset1(k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK4))) = k2_relat_1(sK3)
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_3080])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5982,plain,
    ( k1_setfam_1(k6_enumset1(k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK4))) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5498,c_27,c_28])).

cnf(c_18,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1362,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1372,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1374,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4425,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1374])).

cnf(c_5635,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1362,c_4425])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1361,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5796,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5635,c_1361])).

cnf(c_27615,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5982,c_5796])).

cnf(c_29976,plain,
    ( r1_tarski(k2_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_relat_1(sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_27615])).

cnf(c_1354,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3169,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1354,c_1360])).

cnf(c_3479,plain,
    ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3169,c_1377])).

cnf(c_4041,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK3)))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2558,c_3479])).

cnf(c_5986,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK3)))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4041])).

cnf(c_39081,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_tarski(k6_enumset1(k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k1_relat_1(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_29976,c_5986])).

cnf(c_48914,plain,
    ( k1_setfam_1(k6_enumset1(k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_tarski(k6_enumset1(k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k1_relat_1(sK3))))) = k3_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_39081,c_1379])).

cnf(c_82137,plain,
    ( k1_setfam_1(k6_enumset1(k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK4))))) = k3_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3,c_48914])).

cnf(c_87553,plain,
    ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK4))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_82137,c_5796])).

cnf(c_91043,plain,
    ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_87553])).

cnf(c_91058,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k3_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3472,c_91043])).

cnf(c_3470,plain,
    ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_1378])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1358,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2781,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1358,c_1379])).

cnf(c_4400,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK4))) = k1_relat_1(sK3)
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_2781])).

cnf(c_5041,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK4))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4400,c_27,c_28])).

cnf(c_27612,plain,
    ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5041,c_5796])).

cnf(c_28948,plain,
    ( r1_tarski(k1_relat_1(sK3),k3_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3470,c_27612])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91058,c_28948,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 43.63/6.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.63/6.03  
% 43.63/6.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.63/6.03  
% 43.63/6.03  ------  iProver source info
% 43.63/6.03  
% 43.63/6.03  git: date: 2020-06-30 10:37:57 +0100
% 43.63/6.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.63/6.03  git: non_committed_changes: false
% 43.63/6.03  git: last_make_outside_of_git: false
% 43.63/6.03  
% 43.63/6.03  ------ 
% 43.63/6.03  
% 43.63/6.03  ------ Input Options
% 43.63/6.03  
% 43.63/6.03  --out_options                           all
% 43.63/6.03  --tptp_safe_out                         true
% 43.63/6.03  --problem_path                          ""
% 43.63/6.03  --include_path                          ""
% 43.63/6.03  --clausifier                            res/vclausify_rel
% 43.63/6.03  --clausifier_options                    ""
% 43.63/6.03  --stdin                                 false
% 43.63/6.03  --stats_out                             all
% 43.63/6.03  
% 43.63/6.03  ------ General Options
% 43.63/6.03  
% 43.63/6.03  --fof                                   false
% 43.63/6.03  --time_out_real                         305.
% 43.63/6.03  --time_out_virtual                      -1.
% 43.63/6.03  --symbol_type_check                     false
% 43.63/6.03  --clausify_out                          false
% 43.63/6.03  --sig_cnt_out                           false
% 43.63/6.03  --trig_cnt_out                          false
% 43.63/6.03  --trig_cnt_out_tolerance                1.
% 43.63/6.03  --trig_cnt_out_sk_spl                   false
% 43.63/6.03  --abstr_cl_out                          false
% 43.63/6.03  
% 43.63/6.03  ------ Global Options
% 43.63/6.03  
% 43.63/6.03  --schedule                              default
% 43.63/6.03  --add_important_lit                     false
% 43.63/6.03  --prop_solver_per_cl                    1000
% 43.63/6.03  --min_unsat_core                        false
% 43.63/6.03  --soft_assumptions                      false
% 43.63/6.03  --soft_lemma_size                       3
% 43.63/6.03  --prop_impl_unit_size                   0
% 43.63/6.03  --prop_impl_unit                        []
% 43.63/6.03  --share_sel_clauses                     true
% 43.63/6.03  --reset_solvers                         false
% 43.63/6.03  --bc_imp_inh                            [conj_cone]
% 43.63/6.03  --conj_cone_tolerance                   3.
% 43.63/6.03  --extra_neg_conj                        none
% 43.63/6.03  --large_theory_mode                     true
% 43.63/6.03  --prolific_symb_bound                   200
% 43.63/6.03  --lt_threshold                          2000
% 43.63/6.03  --clause_weak_htbl                      true
% 43.63/6.03  --gc_record_bc_elim                     false
% 43.63/6.03  
% 43.63/6.03  ------ Preprocessing Options
% 43.63/6.03  
% 43.63/6.03  --preprocessing_flag                    true
% 43.63/6.03  --time_out_prep_mult                    0.1
% 43.63/6.03  --splitting_mode                        input
% 43.63/6.03  --splitting_grd                         true
% 43.63/6.03  --splitting_cvd                         false
% 43.63/6.03  --splitting_cvd_svl                     false
% 43.63/6.03  --splitting_nvd                         32
% 43.63/6.03  --sub_typing                            true
% 43.63/6.03  --prep_gs_sim                           true
% 43.63/6.03  --prep_unflatten                        true
% 43.63/6.03  --prep_res_sim                          true
% 43.63/6.03  --prep_upred                            true
% 43.63/6.03  --prep_sem_filter                       exhaustive
% 43.63/6.03  --prep_sem_filter_out                   false
% 43.63/6.03  --pred_elim                             true
% 43.63/6.03  --res_sim_input                         true
% 43.63/6.03  --eq_ax_congr_red                       true
% 43.63/6.03  --pure_diseq_elim                       true
% 43.63/6.03  --brand_transform                       false
% 43.63/6.03  --non_eq_to_eq                          false
% 43.63/6.03  --prep_def_merge                        true
% 43.63/6.03  --prep_def_merge_prop_impl              false
% 43.63/6.03  --prep_def_merge_mbd                    true
% 43.63/6.03  --prep_def_merge_tr_red                 false
% 43.63/6.03  --prep_def_merge_tr_cl                  false
% 43.63/6.03  --smt_preprocessing                     true
% 43.63/6.03  --smt_ac_axioms                         fast
% 43.63/6.03  --preprocessed_out                      false
% 43.63/6.03  --preprocessed_stats                    false
% 43.63/6.03  
% 43.63/6.03  ------ Abstraction refinement Options
% 43.63/6.03  
% 43.63/6.03  --abstr_ref                             []
% 43.63/6.03  --abstr_ref_prep                        false
% 43.63/6.03  --abstr_ref_until_sat                   false
% 43.63/6.03  --abstr_ref_sig_restrict                funpre
% 43.63/6.03  --abstr_ref_af_restrict_to_split_sk     false
% 43.63/6.03  --abstr_ref_under                       []
% 43.63/6.03  
% 43.63/6.03  ------ SAT Options
% 43.63/6.03  
% 43.63/6.03  --sat_mode                              false
% 43.63/6.03  --sat_fm_restart_options                ""
% 43.63/6.03  --sat_gr_def                            false
% 43.63/6.03  --sat_epr_types                         true
% 43.63/6.03  --sat_non_cyclic_types                  false
% 43.63/6.03  --sat_finite_models                     false
% 43.63/6.03  --sat_fm_lemmas                         false
% 43.63/6.03  --sat_fm_prep                           false
% 43.63/6.03  --sat_fm_uc_incr                        true
% 43.63/6.03  --sat_out_model                         small
% 43.63/6.03  --sat_out_clauses                       false
% 43.63/6.03  
% 43.63/6.03  ------ QBF Options
% 43.63/6.03  
% 43.63/6.03  --qbf_mode                              false
% 43.63/6.03  --qbf_elim_univ                         false
% 43.63/6.03  --qbf_dom_inst                          none
% 43.63/6.03  --qbf_dom_pre_inst                      false
% 43.63/6.03  --qbf_sk_in                             false
% 43.63/6.03  --qbf_pred_elim                         true
% 43.63/6.03  --qbf_split                             512
% 43.63/6.03  
% 43.63/6.03  ------ BMC1 Options
% 43.63/6.03  
% 43.63/6.03  --bmc1_incremental                      false
% 43.63/6.03  --bmc1_axioms                           reachable_all
% 43.63/6.03  --bmc1_min_bound                        0
% 43.63/6.03  --bmc1_max_bound                        -1
% 43.63/6.03  --bmc1_max_bound_default                -1
% 43.63/6.03  --bmc1_symbol_reachability              true
% 43.63/6.03  --bmc1_property_lemmas                  false
% 43.63/6.03  --bmc1_k_induction                      false
% 43.63/6.03  --bmc1_non_equiv_states                 false
% 43.63/6.03  --bmc1_deadlock                         false
% 43.63/6.03  --bmc1_ucm                              false
% 43.63/6.03  --bmc1_add_unsat_core                   none
% 43.63/6.03  --bmc1_unsat_core_children              false
% 43.63/6.03  --bmc1_unsat_core_extrapolate_axioms    false
% 43.63/6.03  --bmc1_out_stat                         full
% 43.63/6.03  --bmc1_ground_init                      false
% 43.63/6.03  --bmc1_pre_inst_next_state              false
% 43.63/6.03  --bmc1_pre_inst_state                   false
% 43.63/6.03  --bmc1_pre_inst_reach_state             false
% 43.63/6.03  --bmc1_out_unsat_core                   false
% 43.63/6.03  --bmc1_aig_witness_out                  false
% 43.63/6.03  --bmc1_verbose                          false
% 43.63/6.03  --bmc1_dump_clauses_tptp                false
% 43.63/6.03  --bmc1_dump_unsat_core_tptp             false
% 43.63/6.03  --bmc1_dump_file                        -
% 43.63/6.03  --bmc1_ucm_expand_uc_limit              128
% 43.63/6.03  --bmc1_ucm_n_expand_iterations          6
% 43.63/6.03  --bmc1_ucm_extend_mode                  1
% 43.63/6.03  --bmc1_ucm_init_mode                    2
% 43.63/6.03  --bmc1_ucm_cone_mode                    none
% 43.63/6.03  --bmc1_ucm_reduced_relation_type        0
% 43.63/6.03  --bmc1_ucm_relax_model                  4
% 43.63/6.03  --bmc1_ucm_full_tr_after_sat            true
% 43.63/6.03  --bmc1_ucm_expand_neg_assumptions       false
% 43.63/6.03  --bmc1_ucm_layered_model                none
% 43.63/6.03  --bmc1_ucm_max_lemma_size               10
% 43.63/6.03  
% 43.63/6.03  ------ AIG Options
% 43.63/6.03  
% 43.63/6.03  --aig_mode                              false
% 43.63/6.03  
% 43.63/6.03  ------ Instantiation Options
% 43.63/6.03  
% 43.63/6.03  --instantiation_flag                    true
% 43.63/6.03  --inst_sos_flag                         true
% 43.63/6.03  --inst_sos_phase                        true
% 43.63/6.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.63/6.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.63/6.03  --inst_lit_sel_side                     num_symb
% 43.63/6.03  --inst_solver_per_active                1400
% 43.63/6.03  --inst_solver_calls_frac                1.
% 43.63/6.03  --inst_passive_queue_type               priority_queues
% 43.63/6.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.63/6.03  --inst_passive_queues_freq              [25;2]
% 43.63/6.03  --inst_dismatching                      true
% 43.63/6.03  --inst_eager_unprocessed_to_passive     true
% 43.63/6.03  --inst_prop_sim_given                   true
% 43.63/6.03  --inst_prop_sim_new                     false
% 43.63/6.03  --inst_subs_new                         false
% 43.63/6.03  --inst_eq_res_simp                      false
% 43.63/6.03  --inst_subs_given                       false
% 43.63/6.03  --inst_orphan_elimination               true
% 43.63/6.03  --inst_learning_loop_flag               true
% 43.63/6.03  --inst_learning_start                   3000
% 43.63/6.03  --inst_learning_factor                  2
% 43.63/6.03  --inst_start_prop_sim_after_learn       3
% 43.63/6.03  --inst_sel_renew                        solver
% 43.63/6.03  --inst_lit_activity_flag                true
% 43.63/6.03  --inst_restr_to_given                   false
% 43.63/6.03  --inst_activity_threshold               500
% 43.63/6.03  --inst_out_proof                        true
% 43.63/6.03  
% 43.63/6.03  ------ Resolution Options
% 43.63/6.03  
% 43.63/6.03  --resolution_flag                       true
% 43.63/6.03  --res_lit_sel                           adaptive
% 43.63/6.03  --res_lit_sel_side                      none
% 43.63/6.03  --res_ordering                          kbo
% 43.63/6.03  --res_to_prop_solver                    active
% 43.63/6.03  --res_prop_simpl_new                    false
% 43.63/6.03  --res_prop_simpl_given                  true
% 43.63/6.03  --res_passive_queue_type                priority_queues
% 43.63/6.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.63/6.03  --res_passive_queues_freq               [15;5]
% 43.63/6.03  --res_forward_subs                      full
% 43.63/6.03  --res_backward_subs                     full
% 43.63/6.03  --res_forward_subs_resolution           true
% 43.63/6.03  --res_backward_subs_resolution          true
% 43.63/6.03  --res_orphan_elimination                true
% 43.63/6.03  --res_time_limit                        2.
% 43.63/6.03  --res_out_proof                         true
% 43.63/6.03  
% 43.63/6.03  ------ Superposition Options
% 43.63/6.03  
% 43.63/6.03  --superposition_flag                    true
% 43.63/6.03  --sup_passive_queue_type                priority_queues
% 43.63/6.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.63/6.03  --sup_passive_queues_freq               [8;1;4]
% 43.63/6.03  --demod_completeness_check              fast
% 43.63/6.03  --demod_use_ground                      true
% 43.63/6.03  --sup_to_prop_solver                    passive
% 43.63/6.03  --sup_prop_simpl_new                    true
% 43.63/6.03  --sup_prop_simpl_given                  true
% 43.63/6.03  --sup_fun_splitting                     true
% 43.63/6.03  --sup_smt_interval                      50000
% 43.63/6.03  
% 43.63/6.03  ------ Superposition Simplification Setup
% 43.63/6.03  
% 43.63/6.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.63/6.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.63/6.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.63/6.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.63/6.03  --sup_full_triv                         [TrivRules;PropSubs]
% 43.63/6.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.63/6.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.63/6.03  --sup_immed_triv                        [TrivRules]
% 43.63/6.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.63/6.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.63/6.03  --sup_immed_bw_main                     []
% 43.63/6.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.63/6.03  --sup_input_triv                        [Unflattening;TrivRules]
% 43.63/6.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.63/6.03  --sup_input_bw                          []
% 43.63/6.03  
% 43.63/6.03  ------ Combination Options
% 43.63/6.03  
% 43.63/6.03  --comb_res_mult                         3
% 43.63/6.03  --comb_sup_mult                         2
% 43.63/6.03  --comb_inst_mult                        10
% 43.63/6.03  
% 43.63/6.03  ------ Debug Options
% 43.63/6.03  
% 43.63/6.03  --dbg_backtrace                         false
% 43.63/6.03  --dbg_dump_prop_clauses                 false
% 43.63/6.03  --dbg_dump_prop_clauses_file            -
% 43.63/6.03  --dbg_out_stat                          false
% 43.63/6.03  ------ Parsing...
% 43.63/6.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.63/6.03  
% 43.63/6.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 43.63/6.03  
% 43.63/6.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.63/6.03  
% 43.63/6.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.63/6.03  ------ Proving...
% 43.63/6.03  ------ Problem Properties 
% 43.63/6.03  
% 43.63/6.03  
% 43.63/6.03  clauses                                 27
% 43.63/6.03  conjectures                             4
% 43.63/6.03  EPR                                     14
% 43.63/6.03  Horn                                    25
% 43.63/6.03  unary                                   15
% 43.63/6.03  binary                                  3
% 43.63/6.03  lits                                    56
% 43.63/6.03  lits eq                                 12
% 43.63/6.03  fd_pure                                 0
% 43.63/6.03  fd_pseudo                               0
% 43.63/6.03  fd_cond                                 0
% 43.63/6.03  fd_pseudo_cond                          2
% 43.63/6.03  AC symbols                              0
% 43.63/6.03  
% 43.63/6.03  ------ Schedule dynamic 5 is on 
% 43.63/6.03  
% 43.63/6.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 43.63/6.03  
% 43.63/6.03  
% 43.63/6.03  ------ 
% 43.63/6.03  Current options:
% 43.63/6.03  ------ 
% 43.63/6.03  
% 43.63/6.03  ------ Input Options
% 43.63/6.03  
% 43.63/6.03  --out_options                           all
% 43.63/6.03  --tptp_safe_out                         true
% 43.63/6.03  --problem_path                          ""
% 43.63/6.03  --include_path                          ""
% 43.63/6.03  --clausifier                            res/vclausify_rel
% 43.63/6.03  --clausifier_options                    ""
% 43.63/6.03  --stdin                                 false
% 43.63/6.03  --stats_out                             all
% 43.63/6.03  
% 43.63/6.03  ------ General Options
% 43.63/6.03  
% 43.63/6.03  --fof                                   false
% 43.63/6.03  --time_out_real                         305.
% 43.63/6.03  --time_out_virtual                      -1.
% 43.63/6.03  --symbol_type_check                     false
% 43.63/6.03  --clausify_out                          false
% 43.63/6.03  --sig_cnt_out                           false
% 43.63/6.03  --trig_cnt_out                          false
% 43.63/6.03  --trig_cnt_out_tolerance                1.
% 43.63/6.03  --trig_cnt_out_sk_spl                   false
% 43.63/6.03  --abstr_cl_out                          false
% 43.63/6.03  
% 43.63/6.03  ------ Global Options
% 43.63/6.03  
% 43.63/6.03  --schedule                              default
% 43.63/6.03  --add_important_lit                     false
% 43.63/6.03  --prop_solver_per_cl                    1000
% 43.63/6.03  --min_unsat_core                        false
% 43.63/6.03  --soft_assumptions                      false
% 43.63/6.03  --soft_lemma_size                       3
% 43.63/6.03  --prop_impl_unit_size                   0
% 43.63/6.03  --prop_impl_unit                        []
% 43.63/6.03  --share_sel_clauses                     true
% 43.63/6.03  --reset_solvers                         false
% 43.63/6.03  --bc_imp_inh                            [conj_cone]
% 43.63/6.03  --conj_cone_tolerance                   3.
% 43.63/6.03  --extra_neg_conj                        none
% 43.63/6.03  --large_theory_mode                     true
% 43.63/6.03  --prolific_symb_bound                   200
% 43.63/6.03  --lt_threshold                          2000
% 43.63/6.03  --clause_weak_htbl                      true
% 43.63/6.03  --gc_record_bc_elim                     false
% 43.63/6.03  
% 43.63/6.03  ------ Preprocessing Options
% 43.63/6.03  
% 43.63/6.03  --preprocessing_flag                    true
% 43.63/6.03  --time_out_prep_mult                    0.1
% 43.63/6.03  --splitting_mode                        input
% 43.63/6.03  --splitting_grd                         true
% 43.63/6.03  --splitting_cvd                         false
% 43.63/6.03  --splitting_cvd_svl                     false
% 43.63/6.03  --splitting_nvd                         32
% 43.63/6.03  --sub_typing                            true
% 43.63/6.03  --prep_gs_sim                           true
% 43.63/6.03  --prep_unflatten                        true
% 43.63/6.03  --prep_res_sim                          true
% 43.63/6.03  --prep_upred                            true
% 43.63/6.03  --prep_sem_filter                       exhaustive
% 43.63/6.03  --prep_sem_filter_out                   false
% 43.63/6.03  --pred_elim                             true
% 43.63/6.03  --res_sim_input                         true
% 43.63/6.03  --eq_ax_congr_red                       true
% 43.63/6.03  --pure_diseq_elim                       true
% 43.63/6.03  --brand_transform                       false
% 43.63/6.03  --non_eq_to_eq                          false
% 43.63/6.03  --prep_def_merge                        true
% 43.63/6.03  --prep_def_merge_prop_impl              false
% 43.63/6.03  --prep_def_merge_mbd                    true
% 43.63/6.03  --prep_def_merge_tr_red                 false
% 43.63/6.03  --prep_def_merge_tr_cl                  false
% 43.63/6.03  --smt_preprocessing                     true
% 43.63/6.03  --smt_ac_axioms                         fast
% 43.63/6.03  --preprocessed_out                      false
% 43.63/6.03  --preprocessed_stats                    false
% 43.63/6.03  
% 43.63/6.03  ------ Abstraction refinement Options
% 43.63/6.03  
% 43.63/6.03  --abstr_ref                             []
% 43.63/6.03  --abstr_ref_prep                        false
% 43.63/6.03  --abstr_ref_until_sat                   false
% 43.63/6.03  --abstr_ref_sig_restrict                funpre
% 43.63/6.03  --abstr_ref_af_restrict_to_split_sk     false
% 43.63/6.03  --abstr_ref_under                       []
% 43.63/6.03  
% 43.63/6.03  ------ SAT Options
% 43.63/6.03  
% 43.63/6.03  --sat_mode                              false
% 43.63/6.03  --sat_fm_restart_options                ""
% 43.63/6.03  --sat_gr_def                            false
% 43.63/6.03  --sat_epr_types                         true
% 43.63/6.03  --sat_non_cyclic_types                  false
% 43.63/6.03  --sat_finite_models                     false
% 43.63/6.03  --sat_fm_lemmas                         false
% 43.63/6.03  --sat_fm_prep                           false
% 43.63/6.03  --sat_fm_uc_incr                        true
% 43.63/6.03  --sat_out_model                         small
% 43.63/6.03  --sat_out_clauses                       false
% 43.63/6.03  
% 43.63/6.03  ------ QBF Options
% 43.63/6.03  
% 43.63/6.03  --qbf_mode                              false
% 43.63/6.03  --qbf_elim_univ                         false
% 43.63/6.03  --qbf_dom_inst                          none
% 43.63/6.03  --qbf_dom_pre_inst                      false
% 43.63/6.03  --qbf_sk_in                             false
% 43.63/6.03  --qbf_pred_elim                         true
% 43.63/6.03  --qbf_split                             512
% 43.63/6.03  
% 43.63/6.03  ------ BMC1 Options
% 43.63/6.03  
% 43.63/6.03  --bmc1_incremental                      false
% 43.63/6.03  --bmc1_axioms                           reachable_all
% 43.63/6.03  --bmc1_min_bound                        0
% 43.63/6.03  --bmc1_max_bound                        -1
% 43.63/6.03  --bmc1_max_bound_default                -1
% 43.63/6.03  --bmc1_symbol_reachability              true
% 43.63/6.03  --bmc1_property_lemmas                  false
% 43.63/6.03  --bmc1_k_induction                      false
% 43.63/6.03  --bmc1_non_equiv_states                 false
% 43.63/6.03  --bmc1_deadlock                         false
% 43.63/6.03  --bmc1_ucm                              false
% 43.63/6.03  --bmc1_add_unsat_core                   none
% 43.63/6.03  --bmc1_unsat_core_children              false
% 43.63/6.03  --bmc1_unsat_core_extrapolate_axioms    false
% 43.63/6.03  --bmc1_out_stat                         full
% 43.63/6.03  --bmc1_ground_init                      false
% 43.63/6.03  --bmc1_pre_inst_next_state              false
% 43.63/6.03  --bmc1_pre_inst_state                   false
% 43.63/6.03  --bmc1_pre_inst_reach_state             false
% 43.63/6.03  --bmc1_out_unsat_core                   false
% 43.63/6.03  --bmc1_aig_witness_out                  false
% 43.63/6.03  --bmc1_verbose                          false
% 43.63/6.03  --bmc1_dump_clauses_tptp                false
% 43.63/6.03  --bmc1_dump_unsat_core_tptp             false
% 43.63/6.03  --bmc1_dump_file                        -
% 43.63/6.03  --bmc1_ucm_expand_uc_limit              128
% 43.63/6.03  --bmc1_ucm_n_expand_iterations          6
% 43.63/6.03  --bmc1_ucm_extend_mode                  1
% 43.63/6.03  --bmc1_ucm_init_mode                    2
% 43.63/6.03  --bmc1_ucm_cone_mode                    none
% 43.63/6.03  --bmc1_ucm_reduced_relation_type        0
% 43.63/6.03  --bmc1_ucm_relax_model                  4
% 43.63/6.03  --bmc1_ucm_full_tr_after_sat            true
% 43.63/6.03  --bmc1_ucm_expand_neg_assumptions       false
% 43.63/6.03  --bmc1_ucm_layered_model                none
% 43.63/6.03  --bmc1_ucm_max_lemma_size               10
% 43.63/6.03  
% 43.63/6.03  ------ AIG Options
% 43.63/6.03  
% 43.63/6.03  --aig_mode                              false
% 43.63/6.03  
% 43.63/6.03  ------ Instantiation Options
% 43.63/6.03  
% 43.63/6.03  --instantiation_flag                    true
% 43.63/6.03  --inst_sos_flag                         true
% 43.63/6.03  --inst_sos_phase                        true
% 43.63/6.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 43.63/6.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 43.63/6.03  --inst_lit_sel_side                     none
% 43.63/6.03  --inst_solver_per_active                1400
% 43.63/6.03  --inst_solver_calls_frac                1.
% 43.63/6.03  --inst_passive_queue_type               priority_queues
% 43.63/6.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 43.63/6.03  --inst_passive_queues_freq              [25;2]
% 43.63/6.03  --inst_dismatching                      true
% 43.63/6.03  --inst_eager_unprocessed_to_passive     true
% 43.63/6.03  --inst_prop_sim_given                   true
% 43.63/6.03  --inst_prop_sim_new                     false
% 43.63/6.03  --inst_subs_new                         false
% 43.63/6.03  --inst_eq_res_simp                      false
% 43.63/6.03  --inst_subs_given                       false
% 43.63/6.03  --inst_orphan_elimination               true
% 43.63/6.03  --inst_learning_loop_flag               true
% 43.63/6.03  --inst_learning_start                   3000
% 43.63/6.03  --inst_learning_factor                  2
% 43.63/6.03  --inst_start_prop_sim_after_learn       3
% 43.63/6.03  --inst_sel_renew                        solver
% 43.63/6.03  --inst_lit_activity_flag                true
% 43.63/6.03  --inst_restr_to_given                   false
% 43.63/6.03  --inst_activity_threshold               500
% 43.63/6.03  --inst_out_proof                        true
% 43.63/6.03  
% 43.63/6.03  ------ Resolution Options
% 43.63/6.03  
% 43.63/6.03  --resolution_flag                       false
% 43.63/6.03  --res_lit_sel                           adaptive
% 43.63/6.03  --res_lit_sel_side                      none
% 43.63/6.03  --res_ordering                          kbo
% 43.63/6.03  --res_to_prop_solver                    active
% 43.63/6.03  --res_prop_simpl_new                    false
% 43.63/6.03  --res_prop_simpl_given                  true
% 43.63/6.03  --res_passive_queue_type                priority_queues
% 43.63/6.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 43.63/6.03  --res_passive_queues_freq               [15;5]
% 43.63/6.03  --res_forward_subs                      full
% 43.63/6.03  --res_backward_subs                     full
% 43.63/6.03  --res_forward_subs_resolution           true
% 43.63/6.03  --res_backward_subs_resolution          true
% 43.63/6.03  --res_orphan_elimination                true
% 43.63/6.03  --res_time_limit                        2.
% 43.63/6.03  --res_out_proof                         true
% 43.63/6.03  
% 43.63/6.03  ------ Superposition Options
% 43.63/6.03  
% 43.63/6.03  --superposition_flag                    true
% 43.63/6.03  --sup_passive_queue_type                priority_queues
% 43.63/6.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 43.63/6.03  --sup_passive_queues_freq               [8;1;4]
% 43.63/6.03  --demod_completeness_check              fast
% 43.63/6.03  --demod_use_ground                      true
% 43.63/6.03  --sup_to_prop_solver                    passive
% 43.63/6.03  --sup_prop_simpl_new                    true
% 43.63/6.03  --sup_prop_simpl_given                  true
% 43.63/6.03  --sup_fun_splitting                     true
% 43.63/6.03  --sup_smt_interval                      50000
% 43.63/6.03  
% 43.63/6.03  ------ Superposition Simplification Setup
% 43.63/6.03  
% 43.63/6.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 43.63/6.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 43.63/6.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 43.63/6.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 43.63/6.03  --sup_full_triv                         [TrivRules;PropSubs]
% 43.63/6.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 43.63/6.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 43.63/6.03  --sup_immed_triv                        [TrivRules]
% 43.63/6.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 43.63/6.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.63/6.03  --sup_immed_bw_main                     []
% 43.63/6.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 43.63/6.03  --sup_input_triv                        [Unflattening;TrivRules]
% 43.63/6.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 43.63/6.03  --sup_input_bw                          []
% 43.63/6.03  
% 43.63/6.03  ------ Combination Options
% 43.63/6.03  
% 43.63/6.03  --comb_res_mult                         3
% 43.63/6.03  --comb_sup_mult                         2
% 43.63/6.03  --comb_inst_mult                        10
% 43.63/6.03  
% 43.63/6.03  ------ Debug Options
% 43.63/6.03  
% 43.63/6.03  --dbg_backtrace                         false
% 43.63/6.03  --dbg_dump_prop_clauses                 false
% 43.63/6.03  --dbg_dump_prop_clauses_file            -
% 43.63/6.03  --dbg_out_stat                          false
% 43.63/6.03  
% 43.63/6.03  
% 43.63/6.03  
% 43.63/6.03  
% 43.63/6.03  ------ Proving...
% 43.63/6.03  
% 43.63/6.03  
% 43.63/6.03  % SZS status Theorem for theBenchmark.p
% 43.63/6.03  
% 43.63/6.03  % SZS output start CNFRefutation for theBenchmark.p
% 43.63/6.03  
% 43.63/6.03  fof(f17,conjecture,(
% 43.63/6.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f18,negated_conjecture,(
% 43.63/6.03    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 43.63/6.03    inference(negated_conjecture,[],[f17])).
% 43.63/6.03  
% 43.63/6.03  fof(f28,plain,(
% 43.63/6.03    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 43.63/6.03    inference(ennf_transformation,[],[f18])).
% 43.63/6.03  
% 43.63/6.03  fof(f29,plain,(
% 43.63/6.03    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 43.63/6.03    inference(flattening,[],[f28])).
% 43.63/6.03  
% 43.63/6.03  fof(f42,plain,(
% 43.63/6.03    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK4)) & r1_tarski(X0,sK4) & v1_relat_1(sK4))) )),
% 43.63/6.03    introduced(choice_axiom,[])).
% 43.63/6.03  
% 43.63/6.03  fof(f41,plain,(
% 43.63/6.03    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK3),k3_relat_1(X1)) & r1_tarski(sK3,X1) & v1_relat_1(X1)) & v1_relat_1(sK3))),
% 43.63/6.03    introduced(choice_axiom,[])).
% 43.63/6.03  
% 43.63/6.03  fof(f43,plain,(
% 43.63/6.03    (~r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) & r1_tarski(sK3,sK4) & v1_relat_1(sK4)) & v1_relat_1(sK3)),
% 43.63/6.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f42,f41])).
% 43.63/6.03  
% 43.63/6.03  fof(f76,plain,(
% 43.63/6.03    v1_relat_1(sK4)),
% 43.63/6.03    inference(cnf_transformation,[],[f43])).
% 43.63/6.03  
% 43.63/6.03  fof(f15,axiom,(
% 43.63/6.03    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f25,plain,(
% 43.63/6.03    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 43.63/6.03    inference(ennf_transformation,[],[f15])).
% 43.63/6.03  
% 43.63/6.03  fof(f72,plain,(
% 43.63/6.03    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f25])).
% 43.63/6.03  
% 43.63/6.03  fof(f11,axiom,(
% 43.63/6.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f54,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.63/6.03    inference(cnf_transformation,[],[f11])).
% 43.63/6.03  
% 43.63/6.03  fof(f5,axiom,(
% 43.63/6.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f48,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f5])).
% 43.63/6.03  
% 43.63/6.03  fof(f6,axiom,(
% 43.63/6.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f49,plain,(
% 43.63/6.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f6])).
% 43.63/6.03  
% 43.63/6.03  fof(f7,axiom,(
% 43.63/6.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f50,plain,(
% 43.63/6.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f7])).
% 43.63/6.03  
% 43.63/6.03  fof(f8,axiom,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f51,plain,(
% 43.63/6.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f8])).
% 43.63/6.03  
% 43.63/6.03  fof(f9,axiom,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f52,plain,(
% 43.63/6.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f9])).
% 43.63/6.03  
% 43.63/6.03  fof(f10,axiom,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f53,plain,(
% 43.63/6.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f10])).
% 43.63/6.03  
% 43.63/6.03  fof(f79,plain,(
% 43.63/6.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f52,f53])).
% 43.63/6.03  
% 43.63/6.03  fof(f80,plain,(
% 43.63/6.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f51,f79])).
% 43.63/6.03  
% 43.63/6.03  fof(f81,plain,(
% 43.63/6.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f50,f80])).
% 43.63/6.03  
% 43.63/6.03  fof(f82,plain,(
% 43.63/6.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f49,f81])).
% 43.63/6.03  
% 43.63/6.03  fof(f83,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f48,f82])).
% 43.63/6.03  
% 43.63/6.03  fof(f85,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 43.63/6.03    inference(definition_unfolding,[],[f54,f83])).
% 43.63/6.03  
% 43.63/6.03  fof(f90,plain,(
% 43.63/6.03    ( ! [X0] : (k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f72,f85])).
% 43.63/6.03  
% 43.63/6.03  fof(f4,axiom,(
% 43.63/6.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f47,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f4])).
% 43.63/6.03  
% 43.63/6.03  fof(f89,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f47,f83,f83])).
% 43.63/6.03  
% 43.63/6.03  fof(f2,axiom,(
% 43.63/6.03    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f45,plain,(
% 43.63/6.03    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 43.63/6.03    inference(cnf_transformation,[],[f2])).
% 43.63/6.03  
% 43.63/6.03  fof(f87,plain,(
% 43.63/6.03    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 43.63/6.03    inference(definition_unfolding,[],[f45,f85])).
% 43.63/6.03  
% 43.63/6.03  fof(f3,axiom,(
% 43.63/6.03    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f20,plain,(
% 43.63/6.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 43.63/6.03    inference(ennf_transformation,[],[f3])).
% 43.63/6.03  
% 43.63/6.03  fof(f21,plain,(
% 43.63/6.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 43.63/6.03    inference(flattening,[],[f20])).
% 43.63/6.03  
% 43.63/6.03  fof(f46,plain,(
% 43.63/6.03    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f21])).
% 43.63/6.03  
% 43.63/6.03  fof(f88,plain,(
% 43.63/6.03    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f46,f85])).
% 43.63/6.03  
% 43.63/6.03  fof(f77,plain,(
% 43.63/6.03    r1_tarski(sK3,sK4)),
% 43.63/6.03    inference(cnf_transformation,[],[f43])).
% 43.63/6.03  
% 43.63/6.03  fof(f16,axiom,(
% 43.63/6.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f26,plain,(
% 43.63/6.03    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.63/6.03    inference(ennf_transformation,[],[f16])).
% 43.63/6.03  
% 43.63/6.03  fof(f27,plain,(
% 43.63/6.03    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.63/6.03    inference(flattening,[],[f26])).
% 43.63/6.03  
% 43.63/6.03  fof(f74,plain,(
% 43.63/6.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f27])).
% 43.63/6.03  
% 43.63/6.03  fof(f1,axiom,(
% 43.63/6.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f19,plain,(
% 43.63/6.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 43.63/6.03    inference(ennf_transformation,[],[f1])).
% 43.63/6.03  
% 43.63/6.03  fof(f44,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f19])).
% 43.63/6.03  
% 43.63/6.03  fof(f13,axiom,(
% 43.63/6.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f70,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 43.63/6.03    inference(cnf_transformation,[],[f13])).
% 43.63/6.03  
% 43.63/6.03  fof(f84,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 43.63/6.03    inference(definition_unfolding,[],[f70,f83])).
% 43.63/6.03  
% 43.63/6.03  fof(f86,plain,(
% 43.63/6.03    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 43.63/6.03    inference(definition_unfolding,[],[f44,f84])).
% 43.63/6.03  
% 43.63/6.03  fof(f75,plain,(
% 43.63/6.03    v1_relat_1(sK3)),
% 43.63/6.03    inference(cnf_transformation,[],[f43])).
% 43.63/6.03  
% 43.63/6.03  fof(f12,axiom,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f22,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 43.63/6.03    inference(ennf_transformation,[],[f12])).
% 43.63/6.03  
% 43.63/6.03  fof(f31,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 43.63/6.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 43.63/6.03  
% 43.63/6.03  fof(f30,plain,(
% 43.63/6.03    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 43.63/6.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 43.63/6.03  
% 43.63/6.03  fof(f32,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 43.63/6.03    inference(definition_folding,[],[f22,f31,f30])).
% 43.63/6.03  
% 43.63/6.03  fof(f40,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 43.63/6.03    inference(nnf_transformation,[],[f32])).
% 43.63/6.03  
% 43.63/6.03  fof(f68,plain,(
% 43.63/6.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 43.63/6.03    inference(cnf_transformation,[],[f40])).
% 43.63/6.03  
% 43.63/6.03  fof(f99,plain,(
% 43.63/6.03    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 43.63/6.03    inference(equality_resolution,[],[f68])).
% 43.63/6.03  
% 43.63/6.03  fof(f37,plain,(
% 43.63/6.03    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 43.63/6.03    inference(nnf_transformation,[],[f30])).
% 43.63/6.03  
% 43.63/6.03  fof(f38,plain,(
% 43.63/6.03    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 43.63/6.03    inference(flattening,[],[f37])).
% 43.63/6.03  
% 43.63/6.03  fof(f39,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 43.63/6.03    inference(rectify,[],[f38])).
% 43.63/6.03  
% 43.63/6.03  fof(f67,plain,(
% 43.63/6.03    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 43.63/6.03    inference(cnf_transformation,[],[f39])).
% 43.63/6.03  
% 43.63/6.03  fof(f91,plain,(
% 43.63/6.03    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 43.63/6.03    inference(equality_resolution,[],[f67])).
% 43.63/6.03  
% 43.63/6.03  fof(f33,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 43.63/6.03    inference(nnf_transformation,[],[f31])).
% 43.63/6.03  
% 43.63/6.03  fof(f34,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 43.63/6.03    inference(rectify,[],[f33])).
% 43.63/6.03  
% 43.63/6.03  fof(f35,plain,(
% 43.63/6.03    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 43.63/6.03    introduced(choice_axiom,[])).
% 43.63/6.03  
% 43.63/6.03  fof(f36,plain,(
% 43.63/6.03    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 43.63/6.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 43.63/6.03  
% 43.63/6.03  fof(f56,plain,(
% 43.63/6.03    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f36])).
% 43.63/6.03  
% 43.63/6.03  fof(f14,axiom,(
% 43.63/6.03    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 43.63/6.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.63/6.03  
% 43.63/6.03  fof(f23,plain,(
% 43.63/6.03    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 43.63/6.03    inference(ennf_transformation,[],[f14])).
% 43.63/6.03  
% 43.63/6.03  fof(f24,plain,(
% 43.63/6.03    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 43.63/6.03    inference(flattening,[],[f23])).
% 43.63/6.03  
% 43.63/6.03  fof(f71,plain,(
% 43.63/6.03    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f24])).
% 43.63/6.03  
% 43.63/6.03  fof(f73,plain,(
% 43.63/6.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.63/6.03    inference(cnf_transformation,[],[f27])).
% 43.63/6.03  
% 43.63/6.03  fof(f78,plain,(
% 43.63/6.03    ~r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4))),
% 43.63/6.03    inference(cnf_transformation,[],[f43])).
% 43.63/6.03  
% 43.63/6.03  cnf(c_25,negated_conjecture,
% 43.63/6.03      ( v1_relat_1(sK4) ),
% 43.63/6.03      inference(cnf_transformation,[],[f76]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1355,plain,
% 43.63/6.03      ( v1_relat_1(sK4) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_20,plain,
% 43.63/6.03      ( ~ v1_relat_1(X0)
% 43.63/6.03      | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 43.63/6.03      inference(cnf_transformation,[],[f90]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1360,plain,
% 43.63/6.03      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 43.63/6.03      | v1_relat_1(X0) != iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_3168,plain,
% 43.63/6.03      ( k3_tarski(k6_enumset1(k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k1_relat_1(sK4),k2_relat_1(sK4))) = k3_relat_1(sK4) ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_1355,c_1360]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_3,plain,
% 43.63/6.03      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 43.63/6.03      inference(cnf_transformation,[],[f89]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1,plain,
% 43.63/6.03      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 43.63/6.03      inference(cnf_transformation,[],[f87]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1378,plain,
% 43.63/6.03      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_2558,plain,
% 43.63/6.03      ( r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_3,c_1378]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_3472,plain,
% 43.63/6.03      ( r1_tarski(k2_relat_1(sK4),k3_relat_1(sK4)) = iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_3168,c_2558]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_2,plain,
% 43.63/6.03      ( ~ r1_tarski(X0,X1)
% 43.63/6.03      | ~ r1_tarski(X2,X1)
% 43.63/6.03      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 43.63/6.03      inference(cnf_transformation,[],[f88]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1377,plain,
% 43.63/6.03      ( r1_tarski(X0,X1) != iProver_top
% 43.63/6.03      | r1_tarski(X2,X1) != iProver_top
% 43.63/6.03      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_24,negated_conjecture,
% 43.63/6.03      ( r1_tarski(sK3,sK4) ),
% 43.63/6.03      inference(cnf_transformation,[],[f77]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1356,plain,
% 43.63/6.03      ( r1_tarski(sK3,sK4) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_21,plain,
% 43.63/6.03      ( ~ r1_tarski(X0,X1)
% 43.63/6.03      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 43.63/6.03      | ~ v1_relat_1(X0)
% 43.63/6.03      | ~ v1_relat_1(X1) ),
% 43.63/6.03      inference(cnf_transformation,[],[f74]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1359,plain,
% 43.63/6.03      ( r1_tarski(X0,X1) != iProver_top
% 43.63/6.03      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 43.63/6.03      | v1_relat_1(X0) != iProver_top
% 43.63/6.03      | v1_relat_1(X1) != iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_0,plain,
% 43.63/6.03      ( ~ r1_tarski(X0,X1)
% 43.63/6.03      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 43.63/6.03      inference(cnf_transformation,[],[f86]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1379,plain,
% 43.63/6.03      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 43.63/6.03      | r1_tarski(X0,X1) != iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_3080,plain,
% 43.63/6.03      ( k1_setfam_1(k6_enumset1(k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(X0)
% 43.63/6.03      | r1_tarski(X0,X1) != iProver_top
% 43.63/6.03      | v1_relat_1(X0) != iProver_top
% 43.63/6.03      | v1_relat_1(X1) != iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_1359,c_1379]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_5498,plain,
% 43.63/6.03      ( k1_setfam_1(k6_enumset1(k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK4))) = k2_relat_1(sK3)
% 43.63/6.03      | v1_relat_1(sK4) != iProver_top
% 43.63/6.03      | v1_relat_1(sK3) != iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_1356,c_3080]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_26,negated_conjecture,
% 43.63/6.03      ( v1_relat_1(sK3) ),
% 43.63/6.03      inference(cnf_transformation,[],[f75]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_27,plain,
% 43.63/6.03      ( v1_relat_1(sK3) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_28,plain,
% 43.63/6.03      ( v1_relat_1(sK4) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_5982,plain,
% 43.63/6.03      ( k1_setfam_1(k6_enumset1(k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK3),k2_relat_1(sK4))) = k2_relat_1(sK3) ),
% 43.63/6.03      inference(global_propositional_subsumption,
% 43.63/6.03                [status(thm)],
% 43.63/6.03                [c_5498,c_27,c_28]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_18,plain,
% 43.63/6.03      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 43.63/6.03      inference(cnf_transformation,[],[f99]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1362,plain,
% 43.63/6.03      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_8,plain,
% 43.63/6.03      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 43.63/6.03      inference(cnf_transformation,[],[f91]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1372,plain,
% 43.63/6.03      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_6,plain,
% 43.63/6.03      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 43.63/6.03      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 43.63/6.03      | r2_hidden(X0,X9) ),
% 43.63/6.03      inference(cnf_transformation,[],[f56]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1374,plain,
% 43.63/6.03      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 43.63/6.03      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 43.63/6.03      | r2_hidden(X0,X9) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_4425,plain,
% 43.63/6.03      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 43.63/6.03      | r2_hidden(X7,X8) = iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_1372,c_1374]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_5635,plain,
% 43.63/6.03      ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_1362,c_4425]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_19,plain,
% 43.63/6.03      ( ~ r2_hidden(X0,X1)
% 43.63/6.03      | ~ r1_tarski(X0,X2)
% 43.63/6.03      | r1_tarski(k1_setfam_1(X1),X2) ),
% 43.63/6.03      inference(cnf_transformation,[],[f71]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_1361,plain,
% 43.63/6.03      ( r2_hidden(X0,X1) != iProver_top
% 43.63/6.03      | r1_tarski(X0,X2) != iProver_top
% 43.63/6.03      | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
% 43.63/6.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_5796,plain,
% 43.63/6.03      ( r1_tarski(X0,X1) != iProver_top
% 43.63/6.03      | r1_tarski(k1_setfam_1(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X0)),X1) = iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_5635,c_1361]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_27615,plain,
% 43.63/6.03      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 43.63/6.03      | r1_tarski(k2_relat_1(sK3),X0) = iProver_top ),
% 43.63/6.03      inference(superposition,[status(thm)],[c_5982,c_5796]) ).
% 43.63/6.03  
% 43.63/6.03  cnf(c_29976,plain,
% 43.63/6.03      ( r1_tarski(k2_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_relat_1(sK4)))) = iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_2558,c_27615]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_1354,plain,
% 43.63/6.04      ( v1_relat_1(sK3) = iProver_top ),
% 43.63/6.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_3169,plain,
% 43.63/6.04      ( k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_1354,c_1360]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_3479,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 43.63/6.04      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 43.63/6.04      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_3169,c_1377]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_4041,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK3)))) = iProver_top
% 43.63/6.04      | r1_tarski(k2_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK3)))) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_2558,c_3479]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_5986,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_relat_1(sK3)))) = iProver_top
% 43.63/6.04      | r1_tarski(k2_relat_1(sK3),k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),X0))) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_3,c_4041]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_39081,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),k3_tarski(k6_enumset1(k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k1_relat_1(sK3)))) = iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_29976,c_5986]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_48914,plain,
% 43.63/6.04      ( k1_setfam_1(k6_enumset1(k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_tarski(k6_enumset1(k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k2_relat_1(sK4),k1_relat_1(sK3))))) = k3_relat_1(sK3) ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_39081,c_1379]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_82137,plain,
% 43.63/6.04      ( k1_setfam_1(k6_enumset1(k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_relat_1(sK3),k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK4))))) = k3_relat_1(sK3) ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_3,c_48914]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_87553,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 43.63/6.04      | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k2_relat_1(sK4))),X0) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_82137,c_5796]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_91043,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),X0) = iProver_top
% 43.63/6.04      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 43.63/6.04      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_1377,c_87553]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_91058,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) = iProver_top
% 43.63/6.04      | r1_tarski(k1_relat_1(sK3),k3_relat_1(sK4)) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_3472,c_91043]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_3470,plain,
% 43.63/6.04      ( r1_tarski(k1_relat_1(sK4),k3_relat_1(sK4)) = iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_3168,c_1378]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_22,plain,
% 43.63/6.04      ( ~ r1_tarski(X0,X1)
% 43.63/6.04      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 43.63/6.04      | ~ v1_relat_1(X0)
% 43.63/6.04      | ~ v1_relat_1(X1) ),
% 43.63/6.04      inference(cnf_transformation,[],[f73]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_1358,plain,
% 43.63/6.04      ( r1_tarski(X0,X1) != iProver_top
% 43.63/6.04      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 43.63/6.04      | v1_relat_1(X0) != iProver_top
% 43.63/6.04      | v1_relat_1(X1) != iProver_top ),
% 43.63/6.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_2781,plain,
% 43.63/6.04      ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(X0)
% 43.63/6.04      | r1_tarski(X0,X1) != iProver_top
% 43.63/6.04      | v1_relat_1(X0) != iProver_top
% 43.63/6.04      | v1_relat_1(X1) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_1358,c_1379]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_4400,plain,
% 43.63/6.04      ( k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK4))) = k1_relat_1(sK3)
% 43.63/6.04      | v1_relat_1(sK4) != iProver_top
% 43.63/6.04      | v1_relat_1(sK3) != iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_1356,c_2781]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_5041,plain,
% 43.63/6.04      ( k1_setfam_1(k6_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK4))) = k1_relat_1(sK3) ),
% 43.63/6.04      inference(global_propositional_subsumption,
% 43.63/6.04                [status(thm)],
% 43.63/6.04                [c_4400,c_27,c_28]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_27612,plain,
% 43.63/6.04      ( r1_tarski(k1_relat_1(sK4),X0) != iProver_top
% 43.63/6.04      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_5041,c_5796]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_28948,plain,
% 43.63/6.04      ( r1_tarski(k1_relat_1(sK3),k3_relat_1(sK4)) = iProver_top ),
% 43.63/6.04      inference(superposition,[status(thm)],[c_3470,c_27612]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_23,negated_conjecture,
% 43.63/6.04      ( ~ r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) ),
% 43.63/6.04      inference(cnf_transformation,[],[f78]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(c_30,plain,
% 43.63/6.04      ( r1_tarski(k3_relat_1(sK3),k3_relat_1(sK4)) != iProver_top ),
% 43.63/6.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 43.63/6.04  
% 43.63/6.04  cnf(contradiction,plain,
% 43.63/6.04      ( $false ),
% 43.63/6.04      inference(minisat,[status(thm)],[c_91058,c_28948,c_30]) ).
% 43.63/6.04  
% 43.63/6.04  
% 43.63/6.04  % SZS output end CNFRefutation for theBenchmark.p
% 43.63/6.04  
% 43.63/6.04  ------                               Statistics
% 43.63/6.04  
% 43.63/6.04  ------ General
% 43.63/6.04  
% 43.63/6.04  abstr_ref_over_cycles:                  0
% 43.63/6.04  abstr_ref_under_cycles:                 0
% 43.63/6.04  gc_basic_clause_elim:                   0
% 43.63/6.04  forced_gc_time:                         0
% 43.63/6.04  parsing_time:                           0.01
% 43.63/6.04  unif_index_cands_time:                  0.
% 43.63/6.04  unif_index_add_time:                    0.
% 43.63/6.04  orderings_time:                         0.
% 43.63/6.04  out_proof_time:                         0.013
% 43.63/6.04  total_time:                             5.126
% 43.63/6.04  num_of_symbols:                         42
% 43.63/6.04  num_of_terms:                           143735
% 43.63/6.04  
% 43.63/6.04  ------ Preprocessing
% 43.63/6.04  
% 43.63/6.04  num_of_splits:                          0
% 43.63/6.04  num_of_split_atoms:                     0
% 43.63/6.04  num_of_reused_defs:                     0
% 43.63/6.04  num_eq_ax_congr_red:                    56
% 43.63/6.04  num_of_sem_filtered_clauses:            1
% 43.63/6.04  num_of_subtypes:                        0
% 43.63/6.04  monotx_restored_types:                  0
% 43.63/6.04  sat_num_of_epr_types:                   0
% 43.63/6.04  sat_num_of_non_cyclic_types:            0
% 43.63/6.04  sat_guarded_non_collapsed_types:        0
% 43.63/6.04  num_pure_diseq_elim:                    0
% 43.63/6.04  simp_replaced_by:                       0
% 43.63/6.04  res_preprocessed:                       104
% 43.63/6.04  prep_upred:                             0
% 43.63/6.04  prep_unflattend:                        306
% 43.63/6.04  smt_new_axioms:                         0
% 43.63/6.04  pred_elim_cands:                        5
% 43.63/6.04  pred_elim:                              0
% 43.63/6.04  pred_elim_cl:                           0
% 43.63/6.04  pred_elim_cycles:                       3
% 43.63/6.04  merged_defs:                            0
% 43.63/6.04  merged_defs_ncl:                        0
% 43.63/6.04  bin_hyper_res:                          0
% 43.63/6.04  prep_cycles:                            3
% 43.63/6.04  pred_elim_time:                         0.01
% 43.63/6.04  splitting_time:                         0.
% 43.63/6.04  sem_filter_time:                        0.
% 43.63/6.04  monotx_time:                            0.
% 43.63/6.04  subtype_inf_time:                       0.
% 43.63/6.04  
% 43.63/6.04  ------ Problem properties
% 43.63/6.04  
% 43.63/6.04  clauses:                                27
% 43.63/6.04  conjectures:                            4
% 43.63/6.04  epr:                                    14
% 43.63/6.04  horn:                                   25
% 43.63/6.04  ground:                                 4
% 43.63/6.04  unary:                                  15
% 43.63/6.04  binary:                                 3
% 43.63/6.04  lits:                                   56
% 43.63/6.04  lits_eq:                                12
% 43.63/6.04  fd_pure:                                0
% 43.63/6.04  fd_pseudo:                              0
% 43.63/6.04  fd_cond:                                0
% 43.63/6.04  fd_pseudo_cond:                         2
% 43.63/6.04  ac_symbols:                             0
% 43.63/6.04  
% 43.63/6.04  ------ Propositional Solver
% 43.63/6.04  
% 43.63/6.04  prop_solver_calls:                      41
% 43.63/6.04  prop_fast_solver_calls:                 1278
% 43.63/6.04  smt_solver_calls:                       0
% 43.63/6.04  smt_fast_solver_calls:                  0
% 43.63/6.04  prop_num_of_clauses:                    39814
% 43.63/6.04  prop_preprocess_simplified:             84168
% 43.63/6.04  prop_fo_subsumed:                       19
% 43.63/6.04  prop_solver_time:                       0.
% 43.63/6.04  smt_solver_time:                        0.
% 43.63/6.04  smt_fast_solver_time:                   0.
% 43.63/6.04  prop_fast_solver_time:                  0.
% 43.63/6.04  prop_unsat_core_time:                   0.002
% 43.63/6.04  
% 43.63/6.04  ------ QBF
% 43.63/6.04  
% 43.63/6.04  qbf_q_res:                              0
% 43.63/6.04  qbf_num_tautologies:                    0
% 43.63/6.04  qbf_prep_cycles:                        0
% 43.63/6.04  
% 43.63/6.04  ------ BMC1
% 43.63/6.04  
% 43.63/6.04  bmc1_current_bound:                     -1
% 43.63/6.04  bmc1_last_solved_bound:                 -1
% 43.63/6.04  bmc1_unsat_core_size:                   -1
% 43.63/6.04  bmc1_unsat_core_parents_size:           -1
% 43.63/6.04  bmc1_merge_next_fun:                    0
% 43.63/6.04  bmc1_unsat_core_clauses_time:           0.
% 43.63/6.04  
% 43.63/6.04  ------ Instantiation
% 43.63/6.04  
% 43.63/6.04  inst_num_of_clauses:                    9348
% 43.63/6.04  inst_num_in_passive:                    7772
% 43.63/6.04  inst_num_in_active:                     1568
% 43.63/6.04  inst_num_in_unprocessed:                8
% 43.63/6.04  inst_num_of_loops:                      1640
% 43.63/6.04  inst_num_of_learning_restarts:          0
% 43.63/6.04  inst_num_moves_active_passive:          71
% 43.63/6.04  inst_lit_activity:                      0
% 43.63/6.04  inst_lit_activity_moves:                0
% 43.63/6.04  inst_num_tautologies:                   0
% 43.63/6.04  inst_num_prop_implied:                  0
% 43.63/6.04  inst_num_existing_simplified:           0
% 43.63/6.04  inst_num_eq_res_simplified:             0
% 43.63/6.04  inst_num_child_elim:                    0
% 43.63/6.04  inst_num_of_dismatching_blockings:      12447
% 43.63/6.04  inst_num_of_non_proper_insts:           8255
% 43.63/6.04  inst_num_of_duplicates:                 0
% 43.63/6.04  inst_inst_num_from_inst_to_res:         0
% 43.63/6.04  inst_dismatching_checking_time:         0.
% 43.63/6.04  
% 43.63/6.04  ------ Resolution
% 43.63/6.04  
% 43.63/6.04  res_num_of_clauses:                     0
% 43.63/6.04  res_num_in_passive:                     0
% 43.63/6.04  res_num_in_active:                      0
% 43.63/6.04  res_num_of_loops:                       107
% 43.63/6.04  res_forward_subset_subsumed:            8887
% 43.63/6.04  res_backward_subset_subsumed:           0
% 43.63/6.04  res_forward_subsumed:                   0
% 43.63/6.04  res_backward_subsumed:                  0
% 43.63/6.04  res_forward_subsumption_resolution:     0
% 43.63/6.04  res_backward_subsumption_resolution:    0
% 43.63/6.04  res_clause_to_clause_subsumption:       28560
% 43.63/6.04  res_orphan_elimination:                 0
% 43.63/6.04  res_tautology_del:                      373
% 43.63/6.04  res_num_eq_res_simplified:              0
% 43.63/6.04  res_num_sel_changes:                    0
% 43.63/6.04  res_moves_from_active_to_pass:          0
% 43.63/6.04  
% 43.63/6.04  ------ Superposition
% 43.63/6.04  
% 43.63/6.04  sup_time_total:                         0.
% 43.63/6.04  sup_time_generating:                    0.
% 43.63/6.04  sup_time_sim_full:                      0.
% 43.63/6.04  sup_time_sim_immed:                     0.
% 43.63/6.04  
% 43.63/6.04  sup_num_of_clauses:                     2400
% 43.63/6.04  sup_num_in_active:                      314
% 43.63/6.04  sup_num_in_passive:                     2086
% 43.63/6.04  sup_num_of_loops:                       327
% 43.63/6.04  sup_fw_superposition:                   3328
% 43.63/6.04  sup_bw_superposition:                   2277
% 43.63/6.04  sup_immediate_simplified:               281
% 43.63/6.04  sup_given_eliminated:                   1
% 43.63/6.04  comparisons_done:                       0
% 43.63/6.04  comparisons_avoided:                    0
% 43.63/6.04  
% 43.63/6.04  ------ Simplifications
% 43.63/6.04  
% 43.63/6.04  
% 43.63/6.04  sim_fw_subset_subsumed:                 23
% 43.63/6.04  sim_bw_subset_subsumed:                 16
% 43.63/6.04  sim_fw_subsumed:                        48
% 43.63/6.04  sim_bw_subsumed:                        14
% 43.63/6.04  sim_fw_subsumption_res:                 0
% 43.63/6.04  sim_bw_subsumption_res:                 0
% 43.63/6.04  sim_tautology_del:                      249
% 43.63/6.04  sim_eq_tautology_del:                   82
% 43.63/6.04  sim_eq_res_simp:                        0
% 43.63/6.04  sim_fw_demodulated:                     69
% 43.63/6.04  sim_bw_demodulated:                     51
% 43.63/6.04  sim_light_normalised:                   106
% 43.63/6.04  sim_joinable_taut:                      0
% 43.63/6.04  sim_joinable_simp:                      0
% 43.63/6.04  sim_ac_normalised:                      0
% 43.63/6.04  sim_smt_subsumption:                    0
% 43.63/6.04  
%------------------------------------------------------------------------------
