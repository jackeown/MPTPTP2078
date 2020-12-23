%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  96 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 136 expanded)
%              Number of equality atoms :   37 (  86 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f40,f47,f56,f59])).

fof(f59,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | ~ spl2_3
    | spl2_4 ),
    inference(subsumption_resolution,[],[f57,f46])).

fof(f46,plain,
    ( sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_3
  <=> sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( sK1 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))
    | spl2_4 ),
    inference(superposition,[],[f55,f27])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f21,f23,f23,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f55,plain,
    ( sK1 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK0))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_4
  <=> sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f41,f37,f53])).

fof(f37,plain,
    ( spl2_2
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( sK1 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK0))))
    | spl2_2 ),
    inference(superposition,[],[f39,f26])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f17,f23,f23])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f39,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f47,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f34,f30,f44])).

fof(f30,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f34,plain,
    ( sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) = X1 ) ),
    inference(definition_unfolding,[],[f22,f23,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f40,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f37])).

fof(f25,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))))) ),
    inference(definition_unfolding,[],[f15,f23,f19,f24,f24])).

fof(f15,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (28097)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (28089)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (28097)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f33,f40,f47,f56,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ~spl2_3 | spl2_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f58])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    $false | (~spl2_3 | spl2_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f57,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl2_3 <=> sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    sK1 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))) | spl2_4),
% 0.20/0.46    inference(superposition,[],[f55,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f21,f23,f23,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f20,f19])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    sK1 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK0)))) | spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl2_4 <=> sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK0))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ~spl2_4 | spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f41,f37,f53])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl2_2 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    sK1 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k1_enumset1(sK0,sK0,sK0)))) | spl2_2),
% 0.20/0.46    inference(superposition,[],[f39,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f17,f23,f23])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))))) | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl2_3 | ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f34,f30,f44])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    sK1 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))) | ~spl2_1),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f32,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_enumset1(X0,X0,X0)))) = X1) )),
% 0.20/0.46    inference(definition_unfolding,[],[f22,f23,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f16,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f30])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ~spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f37])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    sK1 != k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))))),
% 0.20/0.46    inference(definition_unfolding,[],[f15,f23,f19,f24,f24])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f30])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (28097)------------------------------
% 0.20/0.46  % (28097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (28097)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (28097)Memory used [KB]: 10618
% 0.20/0.46  % (28097)Time elapsed: 0.009 s
% 0.20/0.46  % (28097)------------------------------
% 0.20/0.46  % (28097)------------------------------
% 0.20/0.46  % (28092)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (28087)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (28081)Success in time 0.108 s
%------------------------------------------------------------------------------
