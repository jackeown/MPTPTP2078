%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:38 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  110 (1188 expanded)
%              Number of leaves         :   20 ( 381 expanded)
%              Depth                    :   18
%              Number of atoms          :  262 (2427 expanded)
%              Number of equality atoms :   75 (1051 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f687,plain,(
    $false ),
    inference(subsumption_resolution,[],[f686,f328])).

fof(f328,plain,(
    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f83,f85])).

fof(f85,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f51,f80,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f83,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f46,f81,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f80])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f686,plain,(
    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f685,f450])).

fof(f450,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f279,f426])).

fof(f426,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f417,f397])).

fof(f397,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | k1_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f396,f377])).

fof(f377,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f374,f102])).

fof(f102,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f60,f95])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f374,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2)) ),
    inference(resolution,[],[f369,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f74,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f369,plain,(
    ! [X15] : sP0(X15,X15,k1_xboole_0) ),
    inference(resolution,[],[f226,f295])).

fof(f295,plain,(
    ! [X14] : ~ r2_hidden(X14,k1_xboole_0) ),
    inference(superposition,[],[f114,f254])).

fof(f254,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(backward_demodulation,[],[f200,f252])).

fof(f252,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(forward_demodulation,[],[f247,f168])).

fof(f168,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f84,f85])).

fof(f84,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f47,f81])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f247,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4)) ),
    inference(superposition,[],[f87,f168])).

fof(f87,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f56,f81,f54,f81])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f200,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) = X3 ),
    inference(superposition,[],[f86,f168])).

fof(f86,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f55,f81,f54])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f114,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k5_xboole_0(X4,X4)) ),
    inference(subsumption_resolution,[],[f113,f108])).

fof(f108,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X4,X4))
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f67,f103])).

fof(f103,plain,(
    ! [X0] : sP0(X0,X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f97,f102])).

fof(f97,plain,(
    ! [X0,X1] : sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f73,f54])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
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

% (32508)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f113,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(X4,X4))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f68,f103])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f226,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X2,X3] :
      ( sP0(X2,X2,X3)
      | r2_hidden(sK5(X2,X2,X3),X3)
      | r2_hidden(sK5(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f396,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X4,X4) = X3
      | ~ v1_xboole_0(X3) ) ),
    inference(forward_demodulation,[],[f393,f102])).

fof(f393,plain,(
    ! [X4,X3] :
      ( ~ v1_xboole_0(X3)
      | k5_xboole_0(X4,k3_xboole_0(X4,X4)) = X3 ) ),
    inference(resolution,[],[f364,f90])).

fof(f364,plain,(
    ! [X4,X3] :
      ( sP0(X3,X3,X4)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f226,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f417,plain,(
    ! [X0] : v1_xboole_0(k3_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f407,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f407,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k3_xboole_0(k1_xboole_0,X4)) ),
    inference(global_subsumption,[],[f287,f295])).

fof(f287,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k3_xboole_0(k1_xboole_0,X4))
      | r2_hidden(X5,k1_xboole_0) ) ),
    inference(superposition,[],[f107,f254])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f67,f97])).

fof(f279,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f199,f254])).

fof(f199,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f86,f84])).

fof(f685,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f672,f377])).

fof(f672,plain,(
    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f86,f586])).

fof(f586,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(resolution,[],[f517,f45])).

fof(f45,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f517,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,sK2)
      | k3_enumset1(sK1,sK1,sK1,sK1,X10) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,X10),sK2) ) ),
    inference(resolution,[],[f190,f45])).

fof(f190,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X11,X10)
      | ~ r2_hidden(X9,X10)
      | k3_enumset1(X11,X11,X11,X11,X9) = k3_xboole_0(k3_enumset1(X11,X11,X11,X11,X9),X10) ) ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:11:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.55  % (32494)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.57  % (32490)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.57  % (32511)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.63/0.57  % (32498)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.63/0.58  % (32502)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.63/0.58  % (32498)Refutation not found, incomplete strategy% (32498)------------------------------
% 1.63/0.58  % (32498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (32493)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.58  % (32498)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  % (32492)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.63/0.58  
% 1.63/0.58  % (32498)Memory used [KB]: 10746
% 1.63/0.58  % (32498)Time elapsed: 0.137 s
% 1.63/0.58  % (32498)------------------------------
% 1.63/0.58  % (32498)------------------------------
% 1.63/0.58  % (32502)Refutation not found, incomplete strategy% (32502)------------------------------
% 1.63/0.58  % (32502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (32502)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (32502)Memory used [KB]: 1663
% 1.63/0.58  % (32502)Time elapsed: 0.148 s
% 1.63/0.58  % (32502)------------------------------
% 1.63/0.58  % (32502)------------------------------
% 1.63/0.59  % (32512)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.59  % (32506)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.60  % (32491)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.63/0.60  % (32489)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.60  % (32499)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.63/0.60  % (32517)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.60  % (32488)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.60  % (32517)Refutation not found, incomplete strategy% (32517)------------------------------
% 1.63/0.60  % (32517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (32517)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (32517)Memory used [KB]: 1663
% 1.63/0.60  % (32517)Time elapsed: 0.171 s
% 1.63/0.60  % (32517)------------------------------
% 1.63/0.60  % (32517)------------------------------
% 1.63/0.60  % (32509)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.63/0.61  % (32494)Refutation found. Thanks to Tanya!
% 1.63/0.61  % SZS status Theorem for theBenchmark
% 1.63/0.61  % SZS output start Proof for theBenchmark
% 1.63/0.61  fof(f687,plain,(
% 1.63/0.61    $false),
% 1.63/0.61    inference(subsumption_resolution,[],[f686,f328])).
% 1.63/0.61  fof(f328,plain,(
% 1.63/0.61    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.63/0.61    inference(forward_demodulation,[],[f83,f85])).
% 1.63/0.61  fof(f85,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.63/0.61    inference(definition_unfolding,[],[f51,f80,f80])).
% 1.63/0.61  fof(f80,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.63/0.61    inference(definition_unfolding,[],[f53,f79])).
% 1.63/0.61  fof(f79,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.63/0.61    inference(definition_unfolding,[],[f66,f78])).
% 1.63/0.61  fof(f78,plain,(
% 1.63/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f15])).
% 1.63/0.61  fof(f15,axiom,(
% 1.63/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.63/0.61  fof(f66,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f14])).
% 1.63/0.61  fof(f14,axiom,(
% 1.63/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.63/0.61  fof(f53,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f13])).
% 1.63/0.61  fof(f13,axiom,(
% 1.63/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.63/0.61  fof(f51,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f11])).
% 1.63/0.61  fof(f11,axiom,(
% 1.63/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.63/0.61  fof(f83,plain,(
% 1.63/0.61    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.63/0.61    inference(definition_unfolding,[],[f46,f81,f82])).
% 1.63/0.61  fof(f82,plain,(
% 1.63/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.63/0.61    inference(definition_unfolding,[],[f48,f80])).
% 1.63/0.61  fof(f48,plain,(
% 1.63/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f12])).
% 1.63/0.61  fof(f12,axiom,(
% 1.63/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.63/0.61  fof(f81,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.63/0.61    inference(definition_unfolding,[],[f52,f80])).
% 1.63/0.61  fof(f52,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.63/0.61    inference(cnf_transformation,[],[f16])).
% 1.63/0.61  fof(f16,axiom,(
% 1.63/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.63/0.61  fof(f46,plain,(
% 1.63/0.61    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.63/0.61    inference(cnf_transformation,[],[f27])).
% 1.63/0.61  fof(f27,plain,(
% 1.63/0.61    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.63/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f26])).
% 1.63/0.61  fof(f26,plain,(
% 1.63/0.61    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.63/0.61    introduced(choice_axiom,[])).
% 1.63/0.61  fof(f21,plain,(
% 1.63/0.61    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.63/0.61    inference(ennf_transformation,[],[f19])).
% 1.63/0.61  fof(f19,negated_conjecture,(
% 1.63/0.61    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.63/0.61    inference(negated_conjecture,[],[f18])).
% 1.63/0.61  fof(f18,conjecture,(
% 1.63/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.63/0.61  fof(f686,plain,(
% 1.63/0.61    sK2 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.63/0.61    inference(forward_demodulation,[],[f685,f450])).
% 1.63/0.61  fof(f450,plain,(
% 1.63/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.61    inference(backward_demodulation,[],[f279,f426])).
% 1.63/0.61  fof(f426,plain,(
% 1.63/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.63/0.61    inference(resolution,[],[f417,f397])).
% 1.63/0.61  fof(f397,plain,(
% 1.63/0.61    ( ! [X3] : (~v1_xboole_0(X3) | k1_xboole_0 = X3) )),
% 1.63/0.61    inference(forward_demodulation,[],[f396,f377])).
% 1.63/0.61  fof(f377,plain,(
% 1.63/0.61    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 1.63/0.61    inference(forward_demodulation,[],[f374,f102])).
% 1.63/0.61  fof(f102,plain,(
% 1.63/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.63/0.61    inference(resolution,[],[f60,f95])).
% 1.63/0.61  fof(f95,plain,(
% 1.63/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.63/0.61    inference(equality_resolution,[],[f62])).
% 1.63/0.61  fof(f62,plain,(
% 1.63/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.63/0.61    inference(cnf_transformation,[],[f35])).
% 1.63/0.61  fof(f35,plain,(
% 1.63/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.61    inference(flattening,[],[f34])).
% 1.63/0.61  fof(f34,plain,(
% 1.63/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.61    inference(nnf_transformation,[],[f4])).
% 1.63/0.61  fof(f4,axiom,(
% 1.63/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.61  fof(f60,plain,(
% 1.63/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.63/0.61    inference(cnf_transformation,[],[f23])).
% 1.63/0.61  fof(f23,plain,(
% 1.63/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.63/0.61    inference(ennf_transformation,[],[f7])).
% 1.63/0.61  fof(f7,axiom,(
% 1.63/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.63/0.61  fof(f374,plain,(
% 1.63/0.61    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2))) )),
% 1.63/0.61    inference(resolution,[],[f369,f90])).
% 1.63/0.61  fof(f90,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 1.63/0.61    inference(definition_unfolding,[],[f74,f54])).
% 1.63/0.61  fof(f54,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.61    inference(cnf_transformation,[],[f5])).
% 1.63/0.61  fof(f5,axiom,(
% 1.63/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.61  fof(f74,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f42])).
% 1.63/0.61  fof(f42,plain,(
% 1.63/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.63/0.61    inference(nnf_transformation,[],[f25])).
% 1.63/0.61  fof(f25,plain,(
% 1.63/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.63/0.61    inference(definition_folding,[],[f2,f24])).
% 1.63/0.61  fof(f24,plain,(
% 1.63/0.61    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.63/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.63/0.61  fof(f2,axiom,(
% 1.63/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.63/0.61  fof(f369,plain,(
% 1.63/0.61    ( ! [X15] : (sP0(X15,X15,k1_xboole_0)) )),
% 1.63/0.61    inference(resolution,[],[f226,f295])).
% 1.63/0.61  fof(f295,plain,(
% 1.63/0.61    ( ! [X14] : (~r2_hidden(X14,k1_xboole_0)) )),
% 1.63/0.61    inference(superposition,[],[f114,f254])).
% 1.63/0.61  fof(f254,plain,(
% 1.63/0.61    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 1.63/0.61    inference(backward_demodulation,[],[f200,f252])).
% 1.63/0.61  fof(f252,plain,(
% 1.63/0.61    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4) )),
% 1.63/0.61    inference(forward_demodulation,[],[f247,f168])).
% 1.63/0.61  fof(f168,plain,(
% 1.63/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.63/0.61    inference(superposition,[],[f84,f85])).
% 1.63/0.61  fof(f84,plain,(
% 1.63/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.63/0.61    inference(definition_unfolding,[],[f47,f81])).
% 1.63/0.61  fof(f47,plain,(
% 1.63/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.61    inference(cnf_transformation,[],[f6])).
% 1.63/0.61  fof(f6,axiom,(
% 1.63/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.63/0.61  fof(f247,plain,(
% 1.63/0.61    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))) )),
% 1.63/0.61    inference(superposition,[],[f87,f168])).
% 1.63/0.61  fof(f87,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.63/0.61    inference(definition_unfolding,[],[f56,f81,f54,f81])).
% 1.63/0.61  fof(f56,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f8])).
% 1.63/0.61  fof(f8,axiom,(
% 1.63/0.61    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.63/0.61  fof(f200,plain,(
% 1.63/0.61    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) = X3) )),
% 1.63/0.61    inference(superposition,[],[f86,f168])).
% 1.63/0.61  fof(f86,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.63/0.61    inference(definition_unfolding,[],[f55,f81,f54])).
% 1.63/0.61  fof(f55,plain,(
% 1.63/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.63/0.61    inference(cnf_transformation,[],[f10])).
% 1.63/0.61  fof(f10,axiom,(
% 1.63/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.63/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.63/0.61  fof(f114,plain,(
% 1.63/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X4))) )),
% 1.63/0.61    inference(subsumption_resolution,[],[f113,f108])).
% 1.63/0.61  fof(f108,plain,(
% 1.63/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X4)) | r2_hidden(X3,X4)) )),
% 1.63/0.61    inference(resolution,[],[f67,f103])).
% 1.63/0.61  fof(f103,plain,(
% 1.63/0.61    ( ! [X0] : (sP0(X0,X0,k5_xboole_0(X0,X0))) )),
% 1.63/0.61    inference(superposition,[],[f97,f102])).
% 1.63/0.61  fof(f97,plain,(
% 1.63/0.61    ( ! [X0,X1] : (sP0(X1,X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.63/0.61    inference(equality_resolution,[],[f91])).
% 1.63/0.61  fof(f91,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.63/0.61    inference(definition_unfolding,[],[f73,f54])).
% 1.63/0.61  fof(f73,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.63/0.61    inference(cnf_transformation,[],[f42])).
% 1.63/0.61  fof(f67,plain,(
% 1.63/0.61    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f41])).
% 1.63/0.61  fof(f41,plain,(
% 1.63/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.63/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 1.63/0.61  fof(f40,plain,(
% 1.63/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.63/0.61    introduced(choice_axiom,[])).
% 1.63/0.61  % (32508)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.63/0.61  fof(f39,plain,(
% 1.63/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.63/0.61    inference(rectify,[],[f38])).
% 1.63/0.61  fof(f38,plain,(
% 1.63/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.63/0.61    inference(flattening,[],[f37])).
% 1.63/0.61  fof(f37,plain,(
% 1.63/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.63/0.61    inference(nnf_transformation,[],[f24])).
% 1.63/0.61  fof(f113,plain,(
% 1.63/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k5_xboole_0(X4,X4)) | ~r2_hidden(X3,X4)) )),
% 1.63/0.61    inference(resolution,[],[f68,f103])).
% 1.63/0.61  fof(f68,plain,(
% 1.63/0.61    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f41])).
% 1.63/0.62  fof(f226,plain,(
% 1.63/0.62    ( ! [X2,X3] : (r2_hidden(sK5(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.63/0.62    inference(duplicate_literal_removal,[],[f224])).
% 1.63/0.62  fof(f224,plain,(
% 1.63/0.62    ( ! [X2,X3] : (sP0(X2,X2,X3) | r2_hidden(sK5(X2,X2,X3),X3) | r2_hidden(sK5(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.63/0.62    inference(resolution,[],[f71,f70])).
% 1.63/0.62  fof(f70,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f41])).
% 1.63/0.62  fof(f71,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f41])).
% 1.63/0.62  fof(f396,plain,(
% 1.63/0.62    ( ! [X4,X3] : (k5_xboole_0(X4,X4) = X3 | ~v1_xboole_0(X3)) )),
% 1.63/0.62    inference(forward_demodulation,[],[f393,f102])).
% 1.63/0.62  fof(f393,plain,(
% 1.63/0.62    ( ! [X4,X3] : (~v1_xboole_0(X3) | k5_xboole_0(X4,k3_xboole_0(X4,X4)) = X3) )),
% 1.63/0.62    inference(resolution,[],[f364,f90])).
% 1.63/0.62  fof(f364,plain,(
% 1.63/0.62    ( ! [X4,X3] : (sP0(X3,X3,X4) | ~v1_xboole_0(X4)) )),
% 1.63/0.62    inference(resolution,[],[f226,f49])).
% 1.63/0.62  fof(f49,plain,(
% 1.63/0.62    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f31])).
% 1.63/0.62  fof(f31,plain,(
% 1.63/0.62    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.63/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.63/0.62  fof(f30,plain,(
% 1.63/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.63/0.62    introduced(choice_axiom,[])).
% 1.63/0.62  fof(f29,plain,(
% 1.63/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.63/0.62    inference(rectify,[],[f28])).
% 1.63/0.62  fof(f28,plain,(
% 1.63/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.63/0.62    inference(nnf_transformation,[],[f1])).
% 1.63/0.62  fof(f1,axiom,(
% 1.63/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.63/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.63/0.62  fof(f417,plain,(
% 1.63/0.62    ( ! [X0] : (v1_xboole_0(k3_xboole_0(k1_xboole_0,X0))) )),
% 1.63/0.62    inference(resolution,[],[f407,f50])).
% 1.63/0.62  fof(f50,plain,(
% 1.63/0.62    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f31])).
% 1.63/0.62  fof(f407,plain,(
% 1.63/0.62    ( ! [X4,X3] : (~r2_hidden(X3,k3_xboole_0(k1_xboole_0,X4))) )),
% 1.63/0.62    inference(global_subsumption,[],[f287,f295])).
% 1.63/0.62  fof(f287,plain,(
% 1.63/0.62    ( ! [X4,X5] : (~r2_hidden(X5,k3_xboole_0(k1_xboole_0,X4)) | r2_hidden(X5,k1_xboole_0)) )),
% 1.63/0.62    inference(superposition,[],[f107,f254])).
% 1.63/0.62  fof(f107,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r2_hidden(X0,X1)) )),
% 1.63/0.62    inference(resolution,[],[f67,f97])).
% 1.63/0.62  fof(f279,plain,(
% 1.63/0.62    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.63/0.62    inference(backward_demodulation,[],[f199,f254])).
% 1.63/0.62  fof(f199,plain,(
% 1.63/0.62    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.63/0.62    inference(superposition,[],[f86,f84])).
% 1.63/0.62  fof(f685,plain,(
% 1.63/0.62    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.63/0.62    inference(forward_demodulation,[],[f672,f377])).
% 1.63/0.62  fof(f672,plain,(
% 1.63/0.62    k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.63/0.62    inference(superposition,[],[f86,f586])).
% 1.63/0.62  fof(f586,plain,(
% 1.63/0.62    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.63/0.62    inference(resolution,[],[f517,f45])).
% 1.63/0.62  fof(f45,plain,(
% 1.63/0.62    r2_hidden(sK1,sK2)),
% 1.63/0.62    inference(cnf_transformation,[],[f27])).
% 1.63/0.62  fof(f517,plain,(
% 1.63/0.62    ( ! [X10] : (~r2_hidden(X10,sK2) | k3_enumset1(sK1,sK1,sK1,sK1,X10) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,X10),sK2)) )),
% 1.63/0.62    inference(resolution,[],[f190,f45])).
% 1.63/0.62  fof(f190,plain,(
% 1.63/0.62    ( ! [X10,X11,X9] : (~r2_hidden(X11,X10) | ~r2_hidden(X9,X10) | k3_enumset1(X11,X11,X11,X11,X9) = k3_xboole_0(k3_enumset1(X11,X11,X11,X11,X9),X10)) )),
% 1.63/0.62    inference(resolution,[],[f92,f60])).
% 1.63/0.62  fof(f92,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.63/0.62    inference(definition_unfolding,[],[f77,f80])).
% 1.63/0.62  fof(f77,plain,(
% 1.63/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.63/0.62    inference(cnf_transformation,[],[f44])).
% 1.63/0.62  fof(f44,plain,(
% 1.63/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.63/0.62    inference(flattening,[],[f43])).
% 1.63/0.62  fof(f43,plain,(
% 1.63/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.63/0.62    inference(nnf_transformation,[],[f17])).
% 1.63/0.62  fof(f17,axiom,(
% 1.63/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.63/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.63/0.62  % SZS output end Proof for theBenchmark
% 1.63/0.62  % (32494)------------------------------
% 1.63/0.62  % (32494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.62  % (32494)Termination reason: Refutation
% 1.63/0.62  
% 1.63/0.62  % (32494)Memory used [KB]: 11129
% 1.63/0.62  % (32494)Time elapsed: 0.168 s
% 1.63/0.62  % (32494)------------------------------
% 1.63/0.62  % (32494)------------------------------
% 1.63/0.62  % (32487)Success in time 0.251 s
%------------------------------------------------------------------------------
