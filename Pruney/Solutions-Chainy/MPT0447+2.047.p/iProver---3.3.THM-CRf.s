%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:16 EST 2020

% Result     : Theorem 35.79s
% Output     : CNFRefutation 35.79s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 336 expanded)
%              Number of clauses        :   73 (  79 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  535 (1064 expanded)
%              Number of equality atoms :  217 ( 421 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK8))
        & r1_tarski(X0,sK8)
        & v1_relat_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(X1))
          & r1_tarski(sK7,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    & r1_tarski(sK7,sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f34,f57,f56])).

fof(f99,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f103,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f102])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f103])).

fof(f105,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f104])).

fof(f106,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f105])).

fof(f108,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f106])).

fof(f112,plain,(
    ! [X0] :
      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f93,f108])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f110,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f63,f108])).

fof(f100,plain,(
    r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f107,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f87,f106])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f107])).

fof(f98,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f58])).

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

fof(f25,plain,(
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

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
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

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f25,f36,f35])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f121,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f85])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f113,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f84])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f108])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f50])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).

fof(f89,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f123,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f77])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1553,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_26,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1560,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4846,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1553,c_1560])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1582,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5000,plain,
    ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4846,c_1582])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK7,sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1554,plain,
    ( r1_tarski(sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1558,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1583,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4415,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1583])).

cnf(c_101395,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK8))) = k1_relat_1(sK7)
    | v1_relat_1(sK8) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_4415])).

cnf(c_34,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_35,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_36,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_103969,plain,
    ( k1_setfam_1(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK8))) = k1_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_101395,c_35,c_36])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1566,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1576,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1578,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6181,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_1578])).

cnf(c_8666,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_6181])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1565,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8672,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8666,c_1565])).

cnf(c_103974,plain,
    ( r1_tarski(k1_relat_1(sK8),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK7),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_103969,c_8672])).

cnf(c_104603,plain,
    ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5000,c_103974])).

cnf(c_921,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1864,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | k3_relat_1(sK8) != X1
    | k3_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_5906,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),X0)
    | k3_relat_1(sK8) != X0
    | k3_relat_1(sK7) != k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_1864])).

cnf(c_73314,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8))
    | k3_relat_1(sK8) != k3_relat_1(sK8)
    | k3_relat_1(sK7) != k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) ),
    inference(instantiation,[status(thm)],[c_5906])).

cnf(c_73317,plain,
    ( k3_relat_1(sK8) != k3_relat_1(sK8)
    | k3_relat_1(sK7) != k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73314])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_8548,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),X0)
    | ~ r1_tarski(k2_relat_1(sK7),X0)
    | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_73306,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8))
    | ~ r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8))
    | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) ),
    inference(instantiation,[status(thm)],[c_8548])).

cnf(c_73309,plain,
    ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
    | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_73306])).

cnf(c_29,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1922,plain,
    ( r2_hidden(X0,sK8)
    | ~ r2_hidden(X0,sK7) ),
    inference(resolution,[status(thm)],[c_2,c_32])).

cnf(c_2539,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X1,X0),sK7)
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_29,c_1922])).

cnf(c_2731,plain,
    ( ~ r2_hidden(k4_tarski(X1,X0),sK7)
    | r2_hidden(X0,k3_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2539,c_33])).

cnf(c_2732,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
    inference(renaming,[status(thm)],[c_2731])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_5021,plain,
    ( r2_hidden(X0,k3_relat_1(sK8))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(resolution,[status(thm)],[c_2732,c_25])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5160,plain,
    ( ~ r2_hidden(sK2(X0,k3_relat_1(sK8)),k2_relat_1(sK7))
    | r1_tarski(X0,k3_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_5021,c_0])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5681,plain,
    ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(resolution,[status(thm)],[c_5160,c_1])).

cnf(c_5682,plain,
    ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5681])).

cnf(c_920,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1994,plain,
    ( X0 != X1
    | k3_relat_1(sK7) != X1
    | k3_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_2265,plain,
    ( X0 != k3_relat_1(sK7)
    | k3_relat_1(sK7) = X0
    | k3_relat_1(sK7) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_2963,plain,
    ( k3_relat_1(sK7) != k3_relat_1(sK7)
    | k3_relat_1(sK7) = k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
    | k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2265])).

cnf(c_919,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2388,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_929,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_2150,plain,
    ( k3_relat_1(sK8) = k3_relat_1(X0)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_2387,plain,
    ( k3_relat_1(sK8) = k3_relat_1(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_939,plain,
    ( k3_relat_1(sK7) = k3_relat_1(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_77,plain,
    ( sP0(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_74,plain,
    ( ~ sP0(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_50,plain,
    ( ~ v1_relat_1(sK7)
    | k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_38,plain,
    ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_104603,c_73317,c_73309,c_5682,c_2963,c_2388,c_2387,c_939,c_77,c_74,c_50,c_38,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.79/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.79/5.00  
% 35.79/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.79/5.00  
% 35.79/5.00  ------  iProver source info
% 35.79/5.00  
% 35.79/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.79/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.79/5.00  git: non_committed_changes: false
% 35.79/5.00  git: last_make_outside_of_git: false
% 35.79/5.00  
% 35.79/5.00  ------ 
% 35.79/5.00  ------ Parsing...
% 35.79/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.79/5.00  
% 35.79/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.79/5.00  
% 35.79/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.79/5.00  
% 35.79/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.79/5.00  ------ Proving...
% 35.79/5.00  ------ Problem Properties 
% 35.79/5.00  
% 35.79/5.00  
% 35.79/5.00  clauses                                 35
% 35.79/5.00  conjectures                             4
% 35.79/5.00  EPR                                     15
% 35.79/5.00  Horn                                    31
% 35.79/5.00  unary                                   14
% 35.79/5.00  binary                                  7
% 35.79/5.00  lits                                    78
% 35.79/5.00  lits eq                                 13
% 35.79/5.00  fd_pure                                 0
% 35.79/5.00  fd_pseudo                               0
% 35.79/5.00  fd_cond                                 0
% 35.79/5.00  fd_pseudo_cond                          4
% 35.79/5.00  AC symbols                              0
% 35.79/5.00  
% 35.79/5.00  ------ Input Options Time Limit: Unbounded
% 35.79/5.00  
% 35.79/5.00  
% 35.79/5.00  ------ 
% 35.79/5.00  Current options:
% 35.79/5.00  ------ 
% 35.79/5.00  
% 35.79/5.00  
% 35.79/5.00  
% 35.79/5.00  
% 35.79/5.00  ------ Proving...
% 35.79/5.00  
% 35.79/5.00  
% 35.79/5.00  % SZS status Theorem for theBenchmark.p
% 35.79/5.00  
% 35.79/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.79/5.00  
% 35.79/5.00  fof(f19,conjecture,(
% 35.79/5.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f20,negated_conjecture,(
% 35.79/5.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 35.79/5.00    inference(negated_conjecture,[],[f19])).
% 35.79/5.00  
% 35.79/5.00  fof(f33,plain,(
% 35.79/5.00    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.79/5.00    inference(ennf_transformation,[],[f20])).
% 35.79/5.00  
% 35.79/5.00  fof(f34,plain,(
% 35.79/5.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 35.79/5.00    inference(flattening,[],[f33])).
% 35.79/5.00  
% 35.79/5.00  fof(f57,plain,(
% 35.79/5.00    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK8)) & r1_tarski(X0,sK8) & v1_relat_1(sK8))) )),
% 35.79/5.00    introduced(choice_axiom,[])).
% 35.79/5.00  
% 35.79/5.00  fof(f56,plain,(
% 35.79/5.00    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK7),k3_relat_1(X1)) & r1_tarski(sK7,X1) & v1_relat_1(X1)) & v1_relat_1(sK7))),
% 35.79/5.00    introduced(choice_axiom,[])).
% 35.79/5.00  
% 35.79/5.00  fof(f58,plain,(
% 35.79/5.00    (~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) & r1_tarski(sK7,sK8) & v1_relat_1(sK8)) & v1_relat_1(sK7)),
% 35.79/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f34,f57,f56])).
% 35.79/5.00  
% 35.79/5.00  fof(f99,plain,(
% 35.79/5.00    v1_relat_1(sK8)),
% 35.79/5.00    inference(cnf_transformation,[],[f58])).
% 35.79/5.00  
% 35.79/5.00  fof(f16,axiom,(
% 35.79/5.00    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f28,plain,(
% 35.79/5.00    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 35.79/5.00    inference(ennf_transformation,[],[f16])).
% 35.79/5.00  
% 35.79/5.00  fof(f93,plain,(
% 35.79/5.00    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f28])).
% 35.79/5.00  
% 35.79/5.00  fof(f11,axiom,(
% 35.79/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f71,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.79/5.00    inference(cnf_transformation,[],[f11])).
% 35.79/5.00  
% 35.79/5.00  fof(f5,axiom,(
% 35.79/5.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f65,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f5])).
% 35.79/5.00  
% 35.79/5.00  fof(f6,axiom,(
% 35.79/5.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f66,plain,(
% 35.79/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f6])).
% 35.79/5.00  
% 35.79/5.00  fof(f7,axiom,(
% 35.79/5.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f67,plain,(
% 35.79/5.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f7])).
% 35.79/5.00  
% 35.79/5.00  fof(f8,axiom,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f68,plain,(
% 35.79/5.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f8])).
% 35.79/5.00  
% 35.79/5.00  fof(f9,axiom,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f69,plain,(
% 35.79/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f9])).
% 35.79/5.00  
% 35.79/5.00  fof(f10,axiom,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f70,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f10])).
% 35.79/5.00  
% 35.79/5.00  fof(f102,plain,(
% 35.79/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f69,f70])).
% 35.79/5.00  
% 35.79/5.00  fof(f103,plain,(
% 35.79/5.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f68,f102])).
% 35.79/5.00  
% 35.79/5.00  fof(f104,plain,(
% 35.79/5.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f67,f103])).
% 35.79/5.00  
% 35.79/5.00  fof(f105,plain,(
% 35.79/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f66,f104])).
% 35.79/5.00  
% 35.79/5.00  fof(f106,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f65,f105])).
% 35.79/5.00  
% 35.79/5.00  fof(f108,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 35.79/5.00    inference(definition_unfolding,[],[f71,f106])).
% 35.79/5.00  
% 35.79/5.00  fof(f112,plain,(
% 35.79/5.00    ( ! [X0] : (k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f93,f108])).
% 35.79/5.00  
% 35.79/5.00  fof(f3,axiom,(
% 35.79/5.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f63,plain,(
% 35.79/5.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 35.79/5.00    inference(cnf_transformation,[],[f3])).
% 35.79/5.00  
% 35.79/5.00  fof(f110,plain,(
% 35.79/5.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 35.79/5.00    inference(definition_unfolding,[],[f63,f108])).
% 35.79/5.00  
% 35.79/5.00  fof(f100,plain,(
% 35.79/5.00    r1_tarski(sK7,sK8)),
% 35.79/5.00    inference(cnf_transformation,[],[f58])).
% 35.79/5.00  
% 35.79/5.00  fof(f17,axiom,(
% 35.79/5.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f29,plain,(
% 35.79/5.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.79/5.00    inference(ennf_transformation,[],[f17])).
% 35.79/5.00  
% 35.79/5.00  fof(f30,plain,(
% 35.79/5.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.79/5.00    inference(flattening,[],[f29])).
% 35.79/5.00  
% 35.79/5.00  fof(f94,plain,(
% 35.79/5.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f30])).
% 35.79/5.00  
% 35.79/5.00  fof(f2,axiom,(
% 35.79/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f22,plain,(
% 35.79/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.79/5.00    inference(ennf_transformation,[],[f2])).
% 35.79/5.00  
% 35.79/5.00  fof(f62,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f22])).
% 35.79/5.00  
% 35.79/5.00  fof(f13,axiom,(
% 35.79/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f87,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.79/5.00    inference(cnf_transformation,[],[f13])).
% 35.79/5.00  
% 35.79/5.00  fof(f107,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 35.79/5.00    inference(definition_unfolding,[],[f87,f106])).
% 35.79/5.00  
% 35.79/5.00  fof(f109,plain,(
% 35.79/5.00    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f62,f107])).
% 35.79/5.00  
% 35.79/5.00  fof(f98,plain,(
% 35.79/5.00    v1_relat_1(sK7)),
% 35.79/5.00    inference(cnf_transformation,[],[f58])).
% 35.79/5.00  
% 35.79/5.00  fof(f12,axiom,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f25,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 35.79/5.00    inference(ennf_transformation,[],[f12])).
% 35.79/5.00  
% 35.79/5.00  fof(f36,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 35.79/5.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 35.79/5.00  
% 35.79/5.00  fof(f35,plain,(
% 35.79/5.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 35.79/5.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 35.79/5.00  
% 35.79/5.00  fof(f37,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 35.79/5.00    inference(definition_folding,[],[f25,f36,f35])).
% 35.79/5.00  
% 35.79/5.00  fof(f49,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 35.79/5.00    inference(nnf_transformation,[],[f37])).
% 35.79/5.00  
% 35.79/5.00  fof(f85,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 35.79/5.00    inference(cnf_transformation,[],[f49])).
% 35.79/5.00  
% 35.79/5.00  fof(f121,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 35.79/5.00    inference(equality_resolution,[],[f85])).
% 35.79/5.00  
% 35.79/5.00  fof(f46,plain,(
% 35.79/5.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 35.79/5.00    inference(nnf_transformation,[],[f35])).
% 35.79/5.00  
% 35.79/5.00  fof(f47,plain,(
% 35.79/5.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 35.79/5.00    inference(flattening,[],[f46])).
% 35.79/5.00  
% 35.79/5.00  fof(f48,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 35.79/5.00    inference(rectify,[],[f47])).
% 35.79/5.00  
% 35.79/5.00  fof(f84,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 35.79/5.00    inference(cnf_transformation,[],[f48])).
% 35.79/5.00  
% 35.79/5.00  fof(f113,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 35.79/5.00    inference(equality_resolution,[],[f84])).
% 35.79/5.00  
% 35.79/5.00  fof(f42,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 35.79/5.00    inference(nnf_transformation,[],[f36])).
% 35.79/5.00  
% 35.79/5.00  fof(f43,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 35.79/5.00    inference(rectify,[],[f42])).
% 35.79/5.00  
% 35.79/5.00  fof(f44,plain,(
% 35.79/5.00    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 35.79/5.00    introduced(choice_axiom,[])).
% 35.79/5.00  
% 35.79/5.00  fof(f45,plain,(
% 35.79/5.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 35.79/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 35.79/5.00  
% 35.79/5.00  fof(f73,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f45])).
% 35.79/5.00  
% 35.79/5.00  fof(f14,axiom,(
% 35.79/5.00    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f26,plain,(
% 35.79/5.00    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 35.79/5.00    inference(ennf_transformation,[],[f14])).
% 35.79/5.00  
% 35.79/5.00  fof(f27,plain,(
% 35.79/5.00    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 35.79/5.00    inference(flattening,[],[f26])).
% 35.79/5.00  
% 35.79/5.00  fof(f88,plain,(
% 35.79/5.00    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f27])).
% 35.79/5.00  
% 35.79/5.00  fof(f4,axiom,(
% 35.79/5.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f23,plain,(
% 35.79/5.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 35.79/5.00    inference(ennf_transformation,[],[f4])).
% 35.79/5.00  
% 35.79/5.00  fof(f24,plain,(
% 35.79/5.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 35.79/5.00    inference(flattening,[],[f23])).
% 35.79/5.00  
% 35.79/5.00  fof(f64,plain,(
% 35.79/5.00    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f24])).
% 35.79/5.00  
% 35.79/5.00  fof(f111,plain,(
% 35.79/5.00    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 35.79/5.00    inference(definition_unfolding,[],[f64,f108])).
% 35.79/5.00  
% 35.79/5.00  fof(f18,axiom,(
% 35.79/5.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f31,plain,(
% 35.79/5.00    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 35.79/5.00    inference(ennf_transformation,[],[f18])).
% 35.79/5.00  
% 35.79/5.00  fof(f32,plain,(
% 35.79/5.00    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 35.79/5.00    inference(flattening,[],[f31])).
% 35.79/5.00  
% 35.79/5.00  fof(f97,plain,(
% 35.79/5.00    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f32])).
% 35.79/5.00  
% 35.79/5.00  fof(f1,axiom,(
% 35.79/5.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f21,plain,(
% 35.79/5.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 35.79/5.00    inference(ennf_transformation,[],[f1])).
% 35.79/5.00  
% 35.79/5.00  fof(f38,plain,(
% 35.79/5.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 35.79/5.00    inference(nnf_transformation,[],[f21])).
% 35.79/5.00  
% 35.79/5.00  fof(f39,plain,(
% 35.79/5.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.79/5.00    inference(rectify,[],[f38])).
% 35.79/5.00  
% 35.79/5.00  fof(f40,plain,(
% 35.79/5.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 35.79/5.00    introduced(choice_axiom,[])).
% 35.79/5.00  
% 35.79/5.00  fof(f41,plain,(
% 35.79/5.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 35.79/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 35.79/5.00  
% 35.79/5.00  fof(f59,plain,(
% 35.79/5.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f41])).
% 35.79/5.00  
% 35.79/5.00  fof(f15,axiom,(
% 35.79/5.00    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 35.79/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.79/5.00  
% 35.79/5.00  fof(f50,plain,(
% 35.79/5.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 35.79/5.00    inference(nnf_transformation,[],[f15])).
% 35.79/5.00  
% 35.79/5.00  fof(f51,plain,(
% 35.79/5.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 35.79/5.00    inference(rectify,[],[f50])).
% 35.79/5.00  
% 35.79/5.00  fof(f54,plain,(
% 35.79/5.00    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 35.79/5.00    introduced(choice_axiom,[])).
% 35.79/5.00  
% 35.79/5.00  fof(f53,plain,(
% 35.79/5.00    ( ! [X2] : (! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0))) )),
% 35.79/5.00    introduced(choice_axiom,[])).
% 35.79/5.00  
% 35.79/5.00  fof(f52,plain,(
% 35.79/5.00    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 35.79/5.00    introduced(choice_axiom,[])).
% 35.79/5.00  
% 35.79/5.00  fof(f55,plain,(
% 35.79/5.00    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 35.79/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f51,f54,f53,f52])).
% 35.79/5.00  
% 35.79/5.00  fof(f89,plain,(
% 35.79/5.00    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 35.79/5.00    inference(cnf_transformation,[],[f55])).
% 35.79/5.00  
% 35.79/5.00  fof(f123,plain,(
% 35.79/5.00    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 35.79/5.00    inference(equality_resolution,[],[f89])).
% 35.79/5.00  
% 35.79/5.00  fof(f61,plain,(
% 35.79/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f41])).
% 35.79/5.00  
% 35.79/5.00  fof(f60,plain,(
% 35.79/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f41])).
% 35.79/5.00  
% 35.79/5.00  fof(f77,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 35.79/5.00    inference(cnf_transformation,[],[f48])).
% 35.79/5.00  
% 35.79/5.00  fof(f120,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 35.79/5.00    inference(equality_resolution,[],[f77])).
% 35.79/5.00  
% 35.79/5.00  fof(f76,plain,(
% 35.79/5.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 35.79/5.00    inference(cnf_transformation,[],[f48])).
% 35.79/5.00  
% 35.79/5.00  fof(f101,plain,(
% 35.79/5.00    ~r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))),
% 35.79/5.00    inference(cnf_transformation,[],[f58])).
% 35.79/5.00  
% 35.79/5.00  cnf(c_33,negated_conjecture,
% 35.79/5.00      ( v1_relat_1(sK8) ),
% 35.79/5.00      inference(cnf_transformation,[],[f99]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1553,plain,
% 35.79/5.00      ( v1_relat_1(sK8) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_26,plain,
% 35.79/5.00      ( ~ v1_relat_1(X0)
% 35.79/5.00      | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 35.79/5.00      inference(cnf_transformation,[],[f112]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1560,plain,
% 35.79/5.00      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 35.79/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_4846,plain,
% 35.79/5.00      ( k3_tarski(k6_enumset1(k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k1_relat_1(sK8),k2_relat_1(sK8))) = k3_relat_1(sK8) ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_1553,c_1560]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_4,plain,
% 35.79/5.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 35.79/5.00      inference(cnf_transformation,[],[f110]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1582,plain,
% 35.79/5.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_5000,plain,
% 35.79/5.00      ( r1_tarski(k1_relat_1(sK8),k3_relat_1(sK8)) = iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_4846,c_1582]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_32,negated_conjecture,
% 35.79/5.00      ( r1_tarski(sK7,sK8) ),
% 35.79/5.00      inference(cnf_transformation,[],[f100]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1554,plain,
% 35.79/5.00      ( r1_tarski(sK7,sK8) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_28,plain,
% 35.79/5.00      ( ~ r1_tarski(X0,X1)
% 35.79/5.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 35.79/5.00      | ~ v1_relat_1(X0)
% 35.79/5.00      | ~ v1_relat_1(X1) ),
% 35.79/5.00      inference(cnf_transformation,[],[f94]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1558,plain,
% 35.79/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.79/5.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 35.79/5.00      | v1_relat_1(X1) != iProver_top
% 35.79/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_3,plain,
% 35.79/5.00      ( ~ r1_tarski(X0,X1)
% 35.79/5.00      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 35.79/5.00      inference(cnf_transformation,[],[f109]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1583,plain,
% 35.79/5.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 35.79/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_4415,plain,
% 35.79/5.00      ( k1_setfam_1(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(X0)
% 35.79/5.00      | r1_tarski(X0,X1) != iProver_top
% 35.79/5.00      | v1_relat_1(X1) != iProver_top
% 35.79/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_1558,c_1583]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_101395,plain,
% 35.79/5.00      ( k1_setfam_1(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK8))) = k1_relat_1(sK7)
% 35.79/5.00      | v1_relat_1(sK8) != iProver_top
% 35.79/5.00      | v1_relat_1(sK7) != iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_1554,c_4415]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_34,negated_conjecture,
% 35.79/5.00      ( v1_relat_1(sK7) ),
% 35.79/5.00      inference(cnf_transformation,[],[f98]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_35,plain,
% 35.79/5.00      ( v1_relat_1(sK7) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_36,plain,
% 35.79/5.00      ( v1_relat_1(sK8) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_103969,plain,
% 35.79/5.00      ( k1_setfam_1(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK8))) = k1_relat_1(sK7) ),
% 35.79/5.00      inference(global_propositional_subsumption,
% 35.79/5.00                [status(thm)],
% 35.79/5.00                [c_101395,c_35,c_36]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_20,plain,
% 35.79/5.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 35.79/5.00      inference(cnf_transformation,[],[f121]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1566,plain,
% 35.79/5.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_10,plain,
% 35.79/5.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 35.79/5.00      inference(cnf_transformation,[],[f113]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1576,plain,
% 35.79/5.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_8,plain,
% 35.79/5.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 35.79/5.00      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 35.79/5.00      | r2_hidden(X0,X9) ),
% 35.79/5.00      inference(cnf_transformation,[],[f73]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1578,plain,
% 35.79/5.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 35.79/5.00      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 35.79/5.00      | r2_hidden(X0,X9) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_6181,plain,
% 35.79/5.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 35.79/5.00      | r2_hidden(X7,X8) = iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_1576,c_1578]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_8666,plain,
% 35.79/5.00      ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_1566,c_6181]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_21,plain,
% 35.79/5.00      ( ~ r2_hidden(X0,X1)
% 35.79/5.00      | ~ r1_tarski(X0,X2)
% 35.79/5.00      | r1_tarski(k1_setfam_1(X1),X2) ),
% 35.79/5.00      inference(cnf_transformation,[],[f88]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1565,plain,
% 35.79/5.00      ( r2_hidden(X0,X1) != iProver_top
% 35.79/5.00      | r1_tarski(X0,X2) != iProver_top
% 35.79/5.00      | r1_tarski(k1_setfam_1(X1),X2) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_8672,plain,
% 35.79/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.79/5.00      | r1_tarski(k1_setfam_1(k6_enumset1(X2,X3,X4,X5,X6,X7,X8,X0)),X1) = iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_8666,c_1565]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_103974,plain,
% 35.79/5.00      ( r1_tarski(k1_relat_1(sK8),X0) != iProver_top
% 35.79/5.00      | r1_tarski(k1_relat_1(sK7),X0) = iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_103969,c_8672]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_104603,plain,
% 35.79/5.00      ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
% 35.79/5.00      inference(superposition,[status(thm)],[c_5000,c_103974]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_921,plain,
% 35.79/5.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.79/5.00      theory(equality) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1864,plain,
% 35.79/5.00      ( ~ r1_tarski(X0,X1)
% 35.79/5.00      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 35.79/5.00      | k3_relat_1(sK8) != X1
% 35.79/5.00      | k3_relat_1(sK7) != X0 ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_921]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_5906,plain,
% 35.79/5.00      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 35.79/5.00      | ~ r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),X0)
% 35.79/5.00      | k3_relat_1(sK8) != X0
% 35.79/5.00      | k3_relat_1(sK7) != k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_1864]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_73314,plain,
% 35.79/5.00      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8))
% 35.79/5.00      | ~ r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8))
% 35.79/5.00      | k3_relat_1(sK8) != k3_relat_1(sK8)
% 35.79/5.00      | k3_relat_1(sK7) != k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_5906]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_73317,plain,
% 35.79/5.00      ( k3_relat_1(sK8) != k3_relat_1(sK8)
% 35.79/5.00      | k3_relat_1(sK7) != k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 35.79/5.00      | r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) = iProver_top
% 35.79/5.00      | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) != iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_73314]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_5,plain,
% 35.79/5.00      ( ~ r1_tarski(X0,X1)
% 35.79/5.00      | ~ r1_tarski(X2,X1)
% 35.79/5.00      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ),
% 35.79/5.00      inference(cnf_transformation,[],[f111]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_8548,plain,
% 35.79/5.00      ( ~ r1_tarski(k1_relat_1(sK7),X0)
% 35.79/5.00      | ~ r1_tarski(k2_relat_1(sK7),X0)
% 35.79/5.00      | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),X0) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_73306,plain,
% 35.79/5.00      ( ~ r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8))
% 35.79/5.00      | ~ r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8))
% 35.79/5.00      | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_8548]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_73309,plain,
% 35.79/5.00      ( r1_tarski(k1_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
% 35.79/5.00      | r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) != iProver_top
% 35.79/5.00      | r1_tarski(k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))),k3_relat_1(sK8)) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_73306]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_29,plain,
% 35.79/5.00      ( r2_hidden(X0,k3_relat_1(X1))
% 35.79/5.00      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 35.79/5.00      | ~ v1_relat_1(X1) ),
% 35.79/5.00      inference(cnf_transformation,[],[f97]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2,plain,
% 35.79/5.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 35.79/5.00      inference(cnf_transformation,[],[f59]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1922,plain,
% 35.79/5.00      ( r2_hidden(X0,sK8) | ~ r2_hidden(X0,sK7) ),
% 35.79/5.00      inference(resolution,[status(thm)],[c_2,c_32]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2539,plain,
% 35.79/5.00      ( r2_hidden(X0,k3_relat_1(sK8))
% 35.79/5.00      | ~ r2_hidden(k4_tarski(X1,X0),sK7)
% 35.79/5.00      | ~ v1_relat_1(sK8) ),
% 35.79/5.00      inference(resolution,[status(thm)],[c_29,c_1922]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2731,plain,
% 35.79/5.00      ( ~ r2_hidden(k4_tarski(X1,X0),sK7)
% 35.79/5.00      | r2_hidden(X0,k3_relat_1(sK8)) ),
% 35.79/5.00      inference(global_propositional_subsumption,
% 35.79/5.00                [status(thm)],
% 35.79/5.00                [c_2539,c_33]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2732,plain,
% 35.79/5.00      ( r2_hidden(X0,k3_relat_1(sK8))
% 35.79/5.00      | ~ r2_hidden(k4_tarski(X1,X0),sK7) ),
% 35.79/5.00      inference(renaming,[status(thm)],[c_2731]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_25,plain,
% 35.79/5.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 35.79/5.00      | r2_hidden(k4_tarski(sK6(X1,X0),X0),X1) ),
% 35.79/5.00      inference(cnf_transformation,[],[f123]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_5021,plain,
% 35.79/5.00      ( r2_hidden(X0,k3_relat_1(sK8)) | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 35.79/5.00      inference(resolution,[status(thm)],[c_2732,c_25]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_0,plain,
% 35.79/5.00      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 35.79/5.00      inference(cnf_transformation,[],[f61]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_5160,plain,
% 35.79/5.00      ( ~ r2_hidden(sK2(X0,k3_relat_1(sK8)),k2_relat_1(sK7))
% 35.79/5.00      | r1_tarski(X0,k3_relat_1(sK8)) ),
% 35.79/5.00      inference(resolution,[status(thm)],[c_5021,c_0]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1,plain,
% 35.79/5.00      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 35.79/5.00      inference(cnf_transformation,[],[f60]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_5681,plain,
% 35.79/5.00      ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) ),
% 35.79/5.00      inference(resolution,[status(thm)],[c_5160,c_1]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_5682,plain,
% 35.79/5.00      ( r1_tarski(k2_relat_1(sK7),k3_relat_1(sK8)) = iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_5681]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_920,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_1994,plain,
% 35.79/5.00      ( X0 != X1 | k3_relat_1(sK7) != X1 | k3_relat_1(sK7) = X0 ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_920]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2265,plain,
% 35.79/5.00      ( X0 != k3_relat_1(sK7)
% 35.79/5.00      | k3_relat_1(sK7) = X0
% 35.79/5.00      | k3_relat_1(sK7) != k3_relat_1(sK7) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_1994]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2963,plain,
% 35.79/5.00      ( k3_relat_1(sK7) != k3_relat_1(sK7)
% 35.79/5.00      | k3_relat_1(sK7) = k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7)))
% 35.79/5.00      | k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) != k3_relat_1(sK7) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_2265]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_919,plain,( X0 = X0 ),theory(equality) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2388,plain,
% 35.79/5.00      ( sK8 = sK8 ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_919]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_929,plain,
% 35.79/5.00      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 35.79/5.00      theory(equality) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2150,plain,
% 35.79/5.00      ( k3_relat_1(sK8) = k3_relat_1(X0) | sK8 != X0 ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_929]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_2387,plain,
% 35.79/5.00      ( k3_relat_1(sK8) = k3_relat_1(sK8) | sK8 != sK8 ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_2150]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_939,plain,
% 35.79/5.00      ( k3_relat_1(sK7) = k3_relat_1(sK7) | sK7 != sK7 ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_929]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_17,plain,
% 35.79/5.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 35.79/5.00      inference(cnf_transformation,[],[f120]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_77,plain,
% 35.79/5.00      ( sP0(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_17]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_18,plain,
% 35.79/5.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 35.79/5.00      | X8 = X0
% 35.79/5.00      | X7 = X0
% 35.79/5.00      | X6 = X0
% 35.79/5.00      | X5 = X0
% 35.79/5.00      | X4 = X0
% 35.79/5.00      | X3 = X0
% 35.79/5.00      | X2 = X0
% 35.79/5.00      | X1 = X0 ),
% 35.79/5.00      inference(cnf_transformation,[],[f76]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_74,plain,
% 35.79/5.00      ( ~ sP0(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) | sK7 = sK7 ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_18]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_50,plain,
% 35.79/5.00      ( ~ v1_relat_1(sK7)
% 35.79/5.00      | k3_tarski(k6_enumset1(k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k1_relat_1(sK7),k2_relat_1(sK7))) = k3_relat_1(sK7) ),
% 35.79/5.00      inference(instantiation,[status(thm)],[c_26]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_31,negated_conjecture,
% 35.79/5.00      ( ~ r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) ),
% 35.79/5.00      inference(cnf_transformation,[],[f101]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(c_38,plain,
% 35.79/5.00      ( r1_tarski(k3_relat_1(sK7),k3_relat_1(sK8)) != iProver_top ),
% 35.79/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.79/5.00  
% 35.79/5.00  cnf(contradiction,plain,
% 35.79/5.00      ( $false ),
% 35.79/5.00      inference(minisat,
% 35.79/5.00                [status(thm)],
% 35.79/5.00                [c_104603,c_73317,c_73309,c_5682,c_2963,c_2388,c_2387,
% 35.79/5.00                 c_939,c_77,c_74,c_50,c_38,c_34]) ).
% 35.79/5.00  
% 35.79/5.00  
% 35.79/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.79/5.00  
% 35.79/5.00  ------                               Statistics
% 35.79/5.00  
% 35.79/5.00  ------ Selected
% 35.79/5.00  
% 35.79/5.00  total_time:                             4.324
% 35.79/5.00  
%------------------------------------------------------------------------------
