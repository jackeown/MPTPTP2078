%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:06 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 922 expanded)
%              Number of leaves         :   18 ( 300 expanded)
%              Depth                    :   18
%              Number of atoms          :  247 (1822 expanded)
%              Number of equality atoms :   76 ( 822 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1077,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1076,f327])).

fof(f327,plain,(
    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3))) ),
    inference(forward_demodulation,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f46,f75,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f77,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3),sK2)) ),
    inference(definition_unfolding,[],[f43,f76,f75])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f75])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2)
    & r2_hidden(sK3,sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2)
      & r2_hidden(sK3,sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f1076,plain,(
    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3))) ),
    inference(forward_demodulation,[],[f1075,f585])).

fof(f585,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f344,f579])).

fof(f579,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f578,f458])).

fof(f458,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f455,f92])).

fof(f92,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f455,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(resolution,[],[f450,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f69,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f450,plain,(
    ! [X23] : sP0(X23,X23,k1_xboole_0) ),
    inference(resolution,[],[f272,f310])).

fof(f310,plain,(
    ! [X9] : ~ r2_hidden(X9,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,(
    ! [X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | ~ r2_hidden(X9,k1_xboole_0) ) ),
    inference(superposition,[],[f104,f288])).

fof(f288,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(forward_demodulation,[],[f282,f187])).

fof(f187,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f78,f79])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f44,f76])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f282,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4)) ),
    inference(superposition,[],[f81,f187])).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f51,f76,f49,f76])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X5,X4)))
      | ~ r2_hidden(X3,X5) ) ),
    inference(resolution,[],[f63,f93])).

fof(f93,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f91,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f68,f49])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
              & r2_hidden(sK5(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f272,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f269])).

fof(f269,plain,(
    ! [X0,X1] :
      ( sP0(X0,X0,X1)
      | r2_hidden(sK5(X0,X0,X1),X1)
      | r2_hidden(sK5(X0,X0,X1),X1)
      | sP0(X0,X0,X1) ) ),
    inference(resolution,[],[f66,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f578,plain,(
    ! [X4,X3] : k5_xboole_0(X3,X3) = k3_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f572,f92])).

fof(f572,plain,(
    ! [X4,X3] : k3_xboole_0(k1_xboole_0,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X3)) ),
    inference(resolution,[],[f442,f84])).

fof(f442,plain,(
    ! [X4,X3] : sP0(X3,X3,k3_xboole_0(k1_xboole_0,X4)) ),
    inference(resolution,[],[f272,f384])).

fof(f384,plain,(
    ! [X6,X5] : ~ r2_hidden(X6,k3_xboole_0(k1_xboole_0,X5)) ),
    inference(subsumption_resolution,[],[f358,f310])).

fof(f358,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k3_xboole_0(k1_xboole_0,X5))
      | r2_hidden(X6,k1_xboole_0) ) ),
    inference(superposition,[],[f100,f291])).

fof(f291,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(backward_demodulation,[],[f231,f288])).

fof(f231,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) = X3 ),
    inference(superposition,[],[f80,f187])).

fof(f80,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f76,f49])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f62,f91])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f344,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f230,f291])).

fof(f230,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f80,f78])).

fof(f1075,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1045,f458])).

fof(f1045,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3))) = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3))) ),
    inference(superposition,[],[f232,f833])).

fof(f833,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK3) = k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3)) ),
    inference(resolution,[],[f712,f42])).

fof(f42,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f712,plain,(
    ! [X30] :
      ( ~ r2_hidden(X30,sK2)
      | k3_enumset1(sK1,sK1,sK1,sK1,X30) = k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,X30)) ) ),
    inference(forward_demodulation,[],[f704,f45])).

fof(f704,plain,(
    ! [X30] :
      ( ~ r2_hidden(X30,sK2)
      | k3_enumset1(sK1,sK1,sK1,sK1,X30) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,X30),sK2) ) ),
    inference(resolution,[],[f202,f41])).

fof(f41,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f202,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X11,X10)
      | ~ r2_hidden(X9,X10)
      | k3_enumset1(X11,X11,X11,X11,X9) = k3_xboole_0(k3_enumset1(X11,X11,X11,X11,X9),X10) ) ),
    inference(resolution,[],[f86,f55])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f72,f75])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f232,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f80,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (2342)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (2326)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (2338)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (2351)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (2338)Refutation not found, incomplete strategy% (2338)------------------------------
% 0.21/0.52  % (2338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2338)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2338)Memory used [KB]: 1663
% 0.21/0.52  % (2338)Time elapsed: 0.104 s
% 0.21/0.52  % (2338)------------------------------
% 0.21/0.52  % (2338)------------------------------
% 0.21/0.52  % (2324)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (2334)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (2329)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (2328)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (2334)Refutation not found, incomplete strategy% (2334)------------------------------
% 0.21/0.53  % (2334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2327)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (2345)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (2347)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (2339)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (2337)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (2350)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (2330)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (2348)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (2325)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (2331)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (2340)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (2352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (2340)Refutation not found, incomplete strategy% (2340)------------------------------
% 0.21/0.54  % (2340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2340)Memory used [KB]: 10618
% 0.21/0.54  % (2340)Time elapsed: 0.129 s
% 0.21/0.54  % (2340)------------------------------
% 0.21/0.54  % (2340)------------------------------
% 0.21/0.54  % (2346)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.40/0.54  % (2334)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (2334)Memory used [KB]: 10746
% 1.40/0.54  % (2334)Time elapsed: 0.119 s
% 1.40/0.54  % (2334)------------------------------
% 1.40/0.54  % (2334)------------------------------
% 1.40/0.54  % (2343)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.55  % (2349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.55  % (2332)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.55  % (2341)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.55  % (2335)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.40/0.55  % (2341)Refutation not found, incomplete strategy% (2341)------------------------------
% 1.40/0.55  % (2341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (2341)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (2341)Memory used [KB]: 1663
% 1.40/0.55  % (2341)Time elapsed: 0.137 s
% 1.40/0.55  % (2341)------------------------------
% 1.40/0.55  % (2341)------------------------------
% 1.40/0.55  % (2336)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.55  % (2333)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.56  % (2353)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.56/0.56  % (2352)Refutation not found, incomplete strategy% (2352)------------------------------
% 1.56/0.56  % (2352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (2352)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (2352)Memory used [KB]: 10746
% 1.56/0.56  % (2352)Time elapsed: 0.148 s
% 1.56/0.56  % (2352)------------------------------
% 1.56/0.56  % (2352)------------------------------
% 1.56/0.56  % (2353)Refutation not found, incomplete strategy% (2353)------------------------------
% 1.56/0.56  % (2353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (2344)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.56  % (2353)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (2353)Memory used [KB]: 1663
% 1.56/0.56  % (2353)Time elapsed: 0.143 s
% 1.56/0.56  % (2353)------------------------------
% 1.56/0.56  % (2353)------------------------------
% 1.56/0.61  % (2330)Refutation found. Thanks to Tanya!
% 1.56/0.61  % SZS status Theorem for theBenchmark
% 1.56/0.61  % SZS output start Proof for theBenchmark
% 1.56/0.61  fof(f1077,plain,(
% 1.56/0.61    $false),
% 1.56/0.61    inference(subsumption_resolution,[],[f1076,f327])).
% 1.56/0.61  fof(f327,plain,(
% 1.56/0.61    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3)))),
% 1.56/0.61    inference(forward_demodulation,[],[f77,f79])).
% 1.56/0.61  fof(f79,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.56/0.61    inference(definition_unfolding,[],[f46,f75,f75])).
% 1.56/0.61  fof(f75,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.56/0.61    inference(definition_unfolding,[],[f48,f74])).
% 1.56/0.61  fof(f74,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.56/0.61    inference(definition_unfolding,[],[f61,f73])).
% 1.56/0.61  fof(f73,plain,(
% 1.56/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f14])).
% 1.56/0.61  fof(f14,axiom,(
% 1.56/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.56/0.61  fof(f61,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f13])).
% 1.56/0.61  fof(f13,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.61  fof(f48,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f12])).
% 1.56/0.61  fof(f12,axiom,(
% 1.56/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.61  fof(f46,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f11])).
% 1.56/0.61  fof(f11,axiom,(
% 1.56/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.56/0.61  fof(f77,plain,(
% 1.56/0.61    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3),sK2))),
% 1.56/0.61    inference(definition_unfolding,[],[f43,f76,f75])).
% 1.56/0.61  fof(f76,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f47,f75])).
% 1.56/0.61  fof(f47,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f15])).
% 1.56/0.61  fof(f15,axiom,(
% 1.56/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.56/0.61  fof(f43,plain,(
% 1.56/0.61    sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2)),
% 1.56/0.61    inference(cnf_transformation,[],[f27])).
% 1.56/0.61  fof(f27,plain,(
% 1.56/0.61    sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2) & r2_hidden(sK3,sK2) & r2_hidden(sK1,sK2)),
% 1.56/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f26])).
% 1.56/0.61  fof(f26,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2) & r2_hidden(sK3,sK2) & r2_hidden(sK1,sK2))),
% 1.56/0.61    introduced(choice_axiom,[])).
% 1.56/0.61  fof(f21,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.56/0.61    inference(flattening,[],[f20])).
% 1.56/0.61  fof(f20,plain,(
% 1.56/0.61    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.56/0.61    inference(ennf_transformation,[],[f18])).
% 1.56/0.61  fof(f18,negated_conjecture,(
% 1.56/0.61    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.56/0.61    inference(negated_conjecture,[],[f17])).
% 1.56/0.61  fof(f17,conjecture,(
% 1.56/0.61    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.56/0.61  fof(f1076,plain,(
% 1.56/0.61    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3)))),
% 1.56/0.61    inference(forward_demodulation,[],[f1075,f585])).
% 1.56/0.61  fof(f585,plain,(
% 1.56/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.56/0.61    inference(backward_demodulation,[],[f344,f579])).
% 1.56/0.61  fof(f579,plain,(
% 1.56/0.61    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 1.56/0.61    inference(forward_demodulation,[],[f578,f458])).
% 1.56/0.61  fof(f458,plain,(
% 1.56/0.61    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 1.56/0.61    inference(forward_demodulation,[],[f455,f92])).
% 1.56/0.61  fof(f92,plain,(
% 1.56/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.56/0.61    inference(resolution,[],[f55,f89])).
% 1.56/0.61  fof(f89,plain,(
% 1.56/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.61    inference(equality_resolution,[],[f57])).
% 1.56/0.61  fof(f57,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.61    inference(cnf_transformation,[],[f31])).
% 1.56/0.61  fof(f31,plain,(
% 1.56/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.61    inference(flattening,[],[f30])).
% 1.56/0.61  fof(f30,plain,(
% 1.56/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.61    inference(nnf_transformation,[],[f4])).
% 1.56/0.61  fof(f4,axiom,(
% 1.56/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.61  fof(f55,plain,(
% 1.56/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.56/0.61    inference(cnf_transformation,[],[f23])).
% 1.56/0.61  fof(f23,plain,(
% 1.56/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.56/0.61    inference(ennf_transformation,[],[f7])).
% 1.56/0.61  fof(f7,axiom,(
% 1.56/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.56/0.61  fof(f455,plain,(
% 1.56/0.61    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 1.56/0.61    inference(resolution,[],[f450,f84])).
% 1.56/0.61  fof(f84,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.56/0.61    inference(definition_unfolding,[],[f69,f49])).
% 1.56/0.61  fof(f49,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f5])).
% 1.56/0.61  fof(f5,axiom,(
% 1.56/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.56/0.61  fof(f69,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f38])).
% 1.56/0.61  fof(f38,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.56/0.61    inference(nnf_transformation,[],[f25])).
% 1.56/0.61  fof(f25,plain,(
% 1.56/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.56/0.61    inference(definition_folding,[],[f2,f24])).
% 1.56/0.61  fof(f24,plain,(
% 1.56/0.61    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.56/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.56/0.61  fof(f2,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.56/0.61  fof(f450,plain,(
% 1.56/0.61    ( ! [X23] : (sP0(X23,X23,k1_xboole_0)) )),
% 1.56/0.61    inference(resolution,[],[f272,f310])).
% 1.56/0.61  fof(f310,plain,(
% 1.56/0.61    ( ! [X9] : (~r2_hidden(X9,k1_xboole_0)) )),
% 1.56/0.61    inference(duplicate_literal_removal,[],[f302])).
% 1.56/0.61  fof(f302,plain,(
% 1.56/0.61    ( ! [X9] : (~r2_hidden(X9,k1_xboole_0) | ~r2_hidden(X9,k1_xboole_0)) )),
% 1.56/0.61    inference(superposition,[],[f104,f288])).
% 1.56/0.61  fof(f288,plain,(
% 1.56/0.61    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4) )),
% 1.56/0.61    inference(forward_demodulation,[],[f282,f187])).
% 1.56/0.61  fof(f187,plain,(
% 1.56/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.56/0.61    inference(superposition,[],[f78,f79])).
% 1.56/0.61  fof(f78,plain,(
% 1.56/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.56/0.61    inference(definition_unfolding,[],[f44,f76])).
% 1.56/0.61  fof(f44,plain,(
% 1.56/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.56/0.61    inference(cnf_transformation,[],[f6])).
% 1.56/0.61  fof(f6,axiom,(
% 1.56/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.56/0.61  fof(f282,plain,(
% 1.56/0.61    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))) )),
% 1.56/0.61    inference(superposition,[],[f81,f187])).
% 1.56/0.61  fof(f81,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f51,f76,f49,f76])).
% 1.56/0.61  fof(f51,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f8])).
% 1.56/0.61  fof(f8,axiom,(
% 1.56/0.61    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.56/0.61  fof(f104,plain,(
% 1.56/0.61    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(X4,k3_xboole_0(X5,X4))) | ~r2_hidden(X3,X5)) )),
% 1.56/0.61    inference(resolution,[],[f63,f93])).
% 1.56/0.61  fof(f93,plain,(
% 1.56/0.61    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 1.56/0.61    inference(superposition,[],[f91,f45])).
% 1.56/0.61  fof(f45,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f1])).
% 1.56/0.61  fof(f1,axiom,(
% 1.56/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.56/0.61  fof(f91,plain,(
% 1.56/0.61    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.56/0.61    inference(equality_resolution,[],[f85])).
% 1.56/0.61  fof(f85,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.56/0.61    inference(definition_unfolding,[],[f68,f49])).
% 1.56/0.61  fof(f68,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.56/0.61    inference(cnf_transformation,[],[f38])).
% 1.56/0.61  fof(f63,plain,(
% 1.56/0.61    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f37])).
% 1.56/0.61  fof(f37,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.56/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.56/0.61  fof(f36,plain,(
% 1.56/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.56/0.61    introduced(choice_axiom,[])).
% 1.56/0.61  fof(f35,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.56/0.61    inference(rectify,[],[f34])).
% 1.56/0.61  fof(f34,plain,(
% 1.56/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.56/0.61    inference(flattening,[],[f33])).
% 1.56/0.61  fof(f33,plain,(
% 1.56/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.56/0.61    inference(nnf_transformation,[],[f24])).
% 1.56/0.61  fof(f272,plain,(
% 1.56/0.61    ( ! [X0,X1] : (r2_hidden(sK5(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 1.56/0.61    inference(duplicate_literal_removal,[],[f269])).
% 1.56/0.61  fof(f269,plain,(
% 1.56/0.61    ( ! [X0,X1] : (sP0(X0,X0,X1) | r2_hidden(sK5(X0,X0,X1),X1) | r2_hidden(sK5(X0,X0,X1),X1) | sP0(X0,X0,X1)) )),
% 1.56/0.61    inference(resolution,[],[f66,f65])).
% 1.56/0.61  fof(f65,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f37])).
% 1.56/0.61  fof(f66,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f37])).
% 1.56/0.61  fof(f578,plain,(
% 1.56/0.61    ( ! [X4,X3] : (k5_xboole_0(X3,X3) = k3_xboole_0(k1_xboole_0,X4)) )),
% 1.56/0.61    inference(forward_demodulation,[],[f572,f92])).
% 1.56/0.61  fof(f572,plain,(
% 1.56/0.61    ( ! [X4,X3] : (k3_xboole_0(k1_xboole_0,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X3))) )),
% 1.56/0.61    inference(resolution,[],[f442,f84])).
% 1.56/0.61  fof(f442,plain,(
% 1.56/0.61    ( ! [X4,X3] : (sP0(X3,X3,k3_xboole_0(k1_xboole_0,X4))) )),
% 1.56/0.61    inference(resolution,[],[f272,f384])).
% 1.56/0.61  fof(f384,plain,(
% 1.56/0.61    ( ! [X6,X5] : (~r2_hidden(X6,k3_xboole_0(k1_xboole_0,X5))) )),
% 1.56/0.61    inference(subsumption_resolution,[],[f358,f310])).
% 1.56/0.61  fof(f358,plain,(
% 1.56/0.61    ( ! [X6,X5] : (~r2_hidden(X6,k3_xboole_0(k1_xboole_0,X5)) | r2_hidden(X6,k1_xboole_0)) )),
% 1.56/0.61    inference(superposition,[],[f100,f291])).
% 1.56/0.61  fof(f291,plain,(
% 1.56/0.61    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 1.56/0.61    inference(backward_demodulation,[],[f231,f288])).
% 1.56/0.61  fof(f231,plain,(
% 1.56/0.61    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) = X3) )),
% 1.56/0.61    inference(superposition,[],[f80,f187])).
% 1.56/0.61  fof(f80,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.56/0.61    inference(definition_unfolding,[],[f50,f76,f49])).
% 1.56/0.61  fof(f50,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.56/0.61    inference(cnf_transformation,[],[f10])).
% 1.56/0.61  fof(f10,axiom,(
% 1.56/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.56/0.61  fof(f100,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r2_hidden(X0,X1)) )),
% 1.56/0.61    inference(resolution,[],[f62,f91])).
% 1.56/0.61  fof(f62,plain,(
% 1.56/0.61    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f37])).
% 1.56/0.61  fof(f344,plain,(
% 1.56/0.61    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.56/0.61    inference(backward_demodulation,[],[f230,f291])).
% 1.56/0.61  fof(f230,plain,(
% 1.56/0.61    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.56/0.61    inference(superposition,[],[f80,f78])).
% 1.56/0.61  fof(f1075,plain,(
% 1.56/0.61    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3))) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.56/0.61    inference(forward_demodulation,[],[f1045,f458])).
% 1.56/0.61  fof(f1045,plain,(
% 1.56/0.61    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3))) = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK3),k3_enumset1(sK1,sK1,sK1,sK1,sK3)))),
% 1.56/0.61    inference(superposition,[],[f232,f833])).
% 1.56/0.61  fof(f833,plain,(
% 1.56/0.61    k3_enumset1(sK1,sK1,sK1,sK1,sK3) = k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK3))),
% 1.56/0.61    inference(resolution,[],[f712,f42])).
% 1.56/0.61  fof(f42,plain,(
% 1.56/0.61    r2_hidden(sK3,sK2)),
% 1.56/0.61    inference(cnf_transformation,[],[f27])).
% 1.56/0.61  fof(f712,plain,(
% 1.56/0.61    ( ! [X30] : (~r2_hidden(X30,sK2) | k3_enumset1(sK1,sK1,sK1,sK1,X30) = k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,X30))) )),
% 1.56/0.61    inference(forward_demodulation,[],[f704,f45])).
% 1.56/0.61  fof(f704,plain,(
% 1.56/0.61    ( ! [X30] : (~r2_hidden(X30,sK2) | k3_enumset1(sK1,sK1,sK1,sK1,X30) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,X30),sK2)) )),
% 1.56/0.61    inference(resolution,[],[f202,f41])).
% 1.56/0.61  fof(f41,plain,(
% 1.56/0.61    r2_hidden(sK1,sK2)),
% 1.56/0.61    inference(cnf_transformation,[],[f27])).
% 1.56/0.61  fof(f202,plain,(
% 1.56/0.61    ( ! [X10,X11,X9] : (~r2_hidden(X11,X10) | ~r2_hidden(X9,X10) | k3_enumset1(X11,X11,X11,X11,X9) = k3_xboole_0(k3_enumset1(X11,X11,X11,X11,X9),X10)) )),
% 1.56/0.61    inference(resolution,[],[f86,f55])).
% 1.56/0.61  fof(f86,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.56/0.61    inference(definition_unfolding,[],[f72,f75])).
% 1.56/0.61  fof(f72,plain,(
% 1.56/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.56/0.61    inference(cnf_transformation,[],[f40])).
% 1.56/0.61  fof(f40,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.56/0.61    inference(flattening,[],[f39])).
% 1.56/0.61  fof(f39,plain,(
% 1.56/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.56/0.61    inference(nnf_transformation,[],[f16])).
% 1.56/0.61  fof(f16,axiom,(
% 1.56/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.56/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.56/0.61  fof(f232,plain,(
% 1.56/0.61    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 1.56/0.61    inference(superposition,[],[f80,f45])).
% 1.56/0.61  % SZS output end Proof for theBenchmark
% 1.56/0.61  % (2330)------------------------------
% 1.56/0.61  % (2330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (2330)Termination reason: Refutation
% 1.56/0.61  
% 1.56/0.61  % (2330)Memory used [KB]: 11385
% 1.56/0.61  % (2330)Time elapsed: 0.197 s
% 1.56/0.61  % (2330)------------------------------
% 1.56/0.61  % (2330)------------------------------
% 1.56/0.61  % (2323)Success in time 0.246 s
%------------------------------------------------------------------------------
