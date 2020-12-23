%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 198 expanded)
%              Number of leaves         :   16 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 ( 689 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f36,f207,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f207,plain,(
    ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(resolution,[],[f196,f113])).

fof(f113,plain,(
    ! [X2] : ~ sP1(sK3,X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,(
    ! [X2] :
      ( sK3 != sK3
      | ~ sP1(sK3,X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ) ),
    inference(superposition,[],[f106,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)) = X0
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f68,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f17,f16])).

fof(f16,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f106,plain,(
    sK3 != k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(forward_demodulation,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f63,f63])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f66,plain,(
    sK3 != k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f37,f64,f65])).

% (6662)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f37,plain,(
    sK3 != k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK2),sK3)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK3 != k2_xboole_0(k1_tarski(sK2),sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f196,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f195,f131])).

fof(f131,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6,X7,X7),X6)
      | sP1(X6,X7,X7) ) ),
    inference(subsumption_resolution,[],[f128,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f54,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK5(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f128,plain,(
    ! [X6,X7] :
      ( sP1(X6,X7,X7)
      | ~ r2_hidden(sK5(X6,X7,X7),X7)
      | ~ r2_hidden(sK5(X6,X7,X7),X6) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X6,X7] :
      ( sP1(X6,X7,X7)
      | ~ r2_hidden(sK5(X6,X7,X7),X7)
      | ~ r2_hidden(sK5(X6,X7,X7),X6)
      | sP1(X6,X7,X7) ) ),
    inference(resolution,[],[f104,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X1)
      | sP1(X0,X1,X1) ) ),
    inference(factoring,[],[f97])).

fof(f104,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK5(X3,X4,X5),X5)
      | sP1(X3,X4,X5)
      | ~ r2_hidden(sK5(X3,X4,X5),X4)
      | ~ r2_hidden(sK5(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f55,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,sK5(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X0)
      | sP1(X0,X1,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,X1),X0)
      | sP1(X0,X1,X1)
      | ~ r1_tarski(X1,X0)
      | sP1(X0,X1,X1) ) ),
    inference(resolution,[],[f117,f131])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X3)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f98,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f98,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK5(X3,X4,X5),X5)
      | sP1(X3,X4,X5)
      | r2_hidden(sK5(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f36,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (6641)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (6640)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (6637)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (6661)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (6639)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (6649)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6642)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (6639)Refutation not found, incomplete strategy% (6639)------------------------------
% 0.21/0.51  % (6639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  % (6659)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (6639)Memory used [KB]: 10618
% 0.21/0.51  % (6639)Time elapsed: 0.095 s
% 0.21/0.51  % (6639)------------------------------
% 0.21/0.51  % (6639)------------------------------
% 0.21/0.51  % (6659)Refutation not found, incomplete strategy% (6659)------------------------------
% 0.21/0.51  % (6659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6647)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (6647)Refutation not found, incomplete strategy% (6647)------------------------------
% 0.21/0.51  % (6647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6647)Memory used [KB]: 10618
% 0.21/0.51  % (6647)Time elapsed: 0.109 s
% 0.21/0.51  % (6647)------------------------------
% 0.21/0.51  % (6647)------------------------------
% 0.21/0.52  % (6666)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (6663)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (6651)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (6659)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6659)Memory used [KB]: 10618
% 0.21/0.52  % (6659)Time elapsed: 0.097 s
% 0.21/0.52  % (6659)------------------------------
% 0.21/0.52  % (6659)------------------------------
% 0.21/0.52  % (6655)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (6658)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (6648)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (6660)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (6645)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (6648)Refutation not found, incomplete strategy% (6648)------------------------------
% 0.21/0.53  % (6648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6648)Memory used [KB]: 10618
% 0.21/0.53  % (6648)Time elapsed: 0.124 s
% 0.21/0.53  % (6648)------------------------------
% 0.21/0.53  % (6648)------------------------------
% 0.21/0.53  % (6657)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (6638)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (6666)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f207,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f50,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f51,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ~r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.21/0.53    inference(resolution,[],[f196,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X2] : (~sP1(sK3,X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X2] : (sK3 != sK3 | ~sP1(sK3,X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) )),
% 0.21/0.53    inference(superposition,[],[f106,f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)) = X0 | ~sP1(X0,X1,X2)) )),
% 0.21/0.53    inference(superposition,[],[f68,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.21/0.53    inference(definition_folding,[],[f2,f17,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f63])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    sK3 != k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.21/0.53    inference(forward_demodulation,[],[f66,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f63,f63])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    sK3 != k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f64,f65])).
% 0.21/0.53  % (6662)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    sK3 != k2_xboole_0(k1_tarski(sK2),sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    sK3 != k2_xboole_0(k1_tarski(sK2),sK3) & r2_hidden(sK2,sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK3 != k2_xboole_0(k1_tarski(sK2),sK3) & r2_hidden(sK2,sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP1(X0,X1,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f195,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ( ! [X6,X7] : (~r2_hidden(sK5(X6,X7,X7),X6) | sP1(X6,X7,X7)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f97])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X1)) )),
% 0.21/0.53    inference(resolution,[],[f54,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X1,sK5(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X6,X7] : (sP1(X6,X7,X7) | ~r2_hidden(sK5(X6,X7,X7),X7) | ~r2_hidden(sK5(X6,X7,X7),X6)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X6,X7] : (sP1(X6,X7,X7) | ~r2_hidden(sK5(X6,X7,X7),X7) | ~r2_hidden(sK5(X6,X7,X7),X6) | sP1(X6,X7,X7)) )),
% 0.21/0.53    inference(resolution,[],[f104,f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X1) | sP1(X0,X1,X1)) )),
% 0.21/0.53    inference(factoring,[],[f97])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~r2_hidden(sK5(X3,X4,X5),X5) | sP1(X3,X4,X5) | ~r2_hidden(sK5(X3,X4,X5),X4) | ~r2_hidden(sK5(X3,X4,X5),X3)) )),
% 0.21/0.53    inference(resolution,[],[f55,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X1,sK5(X0,X1,X2),X0) | sP1(X0,X1,X2) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X0) | sP1(X0,X1,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f189])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1,X1),X0) | sP1(X0,X1,X1) | ~r1_tarski(X1,X0) | sP1(X0,X1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f117,f131])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X2),X3) | r2_hidden(sK5(X0,X1,X2),X0) | sP1(X0,X1,X2) | ~r1_tarski(X2,X3)) )),
% 0.21/0.53    inference(resolution,[],[f98,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (r2_hidden(sK5(X3,X4,X5),X5) | sP1(X3,X4,X5) | r2_hidden(sK5(X3,X4,X5),X3)) )),
% 0.21/0.53    inference(resolution,[],[f54,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    r2_hidden(sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (6666)------------------------------
% 0.21/0.53  % (6666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6666)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (6666)Memory used [KB]: 1791
% 0.21/0.53  % (6666)Time elapsed: 0.123 s
% 0.21/0.53  % (6666)------------------------------
% 0.21/0.53  % (6666)------------------------------
% 0.21/0.53  % (6652)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (6633)Success in time 0.176 s
%------------------------------------------------------------------------------
