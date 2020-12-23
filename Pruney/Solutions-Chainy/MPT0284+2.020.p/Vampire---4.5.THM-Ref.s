%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  90 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 125 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f136,f164])).

fof(f164,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f160,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X1,X0)) ),
    inference(superposition,[],[f39,f23])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f36,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f160,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl2_2 ),
    inference(resolution,[],[f149,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f149,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f38,f22])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f115,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl2_2
  <=> r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f136,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f133,f113,f109])).

fof(f109,plain,
    ( spl2_1
  <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f133,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f75,f68])).

fof(f68,plain,(
    ~ r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f35,f22])).

fof(f35,plain,(
    ~ r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f34,f28,f28])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(f75,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k3_tarski(k2_enumset1(X5,X5,X5,X6)),X7)
      | ~ r1_tarski(k5_xboole_0(X6,k3_xboole_0(X5,X6)),X7)
      | ~ r1_tarski(X5,X7) ) ),
    inference(superposition,[],[f32,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f37,f22])).

fof(f37,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f27,f34,f28])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f121,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f117,f36])).

fof(f117,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(resolution,[],[f111,f29])).

fof(f111,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f109])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:31:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (5887)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (5878)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (5876)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5879)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (5876)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f121,f136,f164])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    $false | spl2_2),
% 0.21/0.48    inference(resolution,[],[f160,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(superposition,[],[f39,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(superposition,[],[f36,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | spl2_2),
% 0.21/0.48    inference(resolution,[],[f149,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_2),
% 0.21/0.48    inference(resolution,[],[f115,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) | ~r1_tarski(X0,X2)) )),
% 0.21/0.48    inference(superposition,[],[f38,f22])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f31,f28])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl2_2 <=> r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~spl2_1 | ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f133,f113,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl2_1 <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(resolution,[],[f75,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(forward_demodulation,[],[f35,f22])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~r1_tarski(k3_tarski(k2_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(definition_unfolding,[],[f21,f34,f28,f28])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f26,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X6,X7,X5] : (r1_tarski(k3_tarski(k2_enumset1(X5,X5,X5,X6)),X7) | ~r1_tarski(k5_xboole_0(X6,k3_xboole_0(X5,X6)),X7) | ~r1_tarski(X5,X7)) )),
% 0.21/0.48    inference(superposition,[],[f32,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(superposition,[],[f37,f22])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f27,f34,f28])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    $false | spl2_1),
% 0.21/0.48    inference(resolution,[],[f117,f36])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.48    inference(resolution,[],[f111,f29])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5876)------------------------------
% 0.21/0.48  % (5876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5876)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5876)Memory used [KB]: 6140
% 0.21/0.48  % (5876)Time elapsed: 0.057 s
% 0.21/0.48  % (5876)------------------------------
% 0.21/0.48  % (5876)------------------------------
% 0.21/0.48  % (5877)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (5886)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (5884)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (5883)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (5883)Refutation not found, incomplete strategy% (5883)------------------------------
% 0.21/0.48  % (5883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (5883)Memory used [KB]: 10618
% 0.21/0.48  % (5883)Time elapsed: 0.034 s
% 0.21/0.48  % (5883)------------------------------
% 0.21/0.48  % (5883)------------------------------
% 0.21/0.48  % (5881)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (5885)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (5882)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (5872)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (5871)Success in time 0.131 s
%------------------------------------------------------------------------------
