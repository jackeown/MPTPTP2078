%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:50 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 111 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  146 ( 218 expanded)
%              Number of equality atoms :   55 (  90 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f45,f49,f57,f65,f69,f151,f155,f293,f366,f372])).

fof(f372,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | spl2_25 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_4
    | spl2_25 ),
    inference(subsumption_resolution,[],[f368,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f368,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl2_1
    | spl2_25 ),
    inference(superposition,[],[f365,f31])).

fof(f31,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f365,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl2_25 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl2_25
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f366,plain,
    ( ~ spl2_25
    | ~ spl2_1
    | ~ spl2_4
    | spl2_12
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f354,f291,f153,f148,f43,f30,f363])).

fof(f148,plain,
    ( spl2_12
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f153,plain,
    ( spl2_13
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f291,plain,
    ( spl2_22
  <=> ! [X1,X0,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f354,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | ~ spl2_1
    | ~ spl2_4
    | spl2_12
    | ~ spl2_13
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f353,f154])).

fof(f154,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f353,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_4
    | spl2_12
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f352,f31])).

fof(f352,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl2_4
    | spl2_12
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f327,f44])).

fof(f327,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_12
    | ~ spl2_22 ),
    inference(superposition,[],[f150,f292])).

fof(f292,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f291])).

fof(f150,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f293,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f86,f63,f30,f291])).

fof(f63,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f86,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f64,f31])).

fof(f64,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f155,plain,
    ( spl2_13
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f111,f67,f55,f153])).

fof(f55,plain,
    ( spl2_6
  <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f111,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f56,f68])).

fof(f68,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f56,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f151,plain,(
    ~ spl2_12 ),
    inference(avatar_split_clause,[],[f26,f148])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f16,f22,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f65,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f57,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f50,f47,f30,f55])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f50,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f31])).

fof(f48,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f41,f38,f34,f47])).

fof(f34,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f38,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f41,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f38])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f34])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f30])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:33:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.49  % (28407)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.49  % (28403)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.49  % (28415)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.50  % (28412)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.50  % (28414)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.50  % (28413)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.50  % (28410)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.50  % (28404)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.50  % (28406)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.50  % (28402)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (28405)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.51  % (28406)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % (28410)Refutation not found, incomplete strategy% (28410)------------------------------
% 0.23/0.51  % (28410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (28410)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (28410)Memory used [KB]: 10490
% 0.23/0.51  % (28410)Time elapsed: 0.080 s
% 0.23/0.51  % (28410)------------------------------
% 0.23/0.51  % (28410)------------------------------
% 0.23/0.52  % (28411)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f373,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(avatar_sat_refutation,[],[f32,f36,f40,f45,f49,f57,f65,f69,f151,f155,f293,f366,f372])).
% 0.23/0.52  fof(f372,plain,(
% 0.23/0.52    ~spl2_1 | ~spl2_4 | spl2_25),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f371])).
% 0.23/0.52  fof(f371,plain,(
% 0.23/0.52    $false | (~spl2_1 | ~spl2_4 | spl2_25)),
% 0.23/0.52    inference(subsumption_resolution,[],[f368,f44])).
% 0.23/0.52  fof(f44,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_4),
% 0.23/0.52    inference(avatar_component_clause,[],[f43])).
% 0.23/0.52  fof(f43,plain,(
% 0.23/0.52    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.52  fof(f368,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | (~spl2_1 | spl2_25)),
% 0.23/0.52    inference(superposition,[],[f365,f31])).
% 0.23/0.52  fof(f31,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_1),
% 0.23/0.52    inference(avatar_component_clause,[],[f30])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    spl2_1 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.52  fof(f365,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl2_25),
% 0.23/0.52    inference(avatar_component_clause,[],[f363])).
% 0.23/0.52  fof(f363,plain,(
% 0.23/0.52    spl2_25 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.23/0.52  fof(f366,plain,(
% 0.23/0.52    ~spl2_25 | ~spl2_1 | ~spl2_4 | spl2_12 | ~spl2_13 | ~spl2_22),
% 0.23/0.52    inference(avatar_split_clause,[],[f354,f291,f153,f148,f43,f30,f363])).
% 0.23/0.52  fof(f148,plain,(
% 0.23/0.52    spl2_12 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.23/0.52  fof(f153,plain,(
% 0.23/0.52    spl2_13 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.23/0.52  fof(f291,plain,(
% 0.23/0.52    spl2_22 <=> ! [X1,X0,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.23/0.52  fof(f354,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | (~spl2_1 | ~spl2_4 | spl2_12 | ~spl2_13 | ~spl2_22)),
% 0.23/0.52    inference(forward_demodulation,[],[f353,f154])).
% 0.23/0.52  fof(f154,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl2_13),
% 0.23/0.52    inference(avatar_component_clause,[],[f153])).
% 0.23/0.52  fof(f353,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl2_1 | ~spl2_4 | spl2_12 | ~spl2_22)),
% 0.23/0.52    inference(forward_demodulation,[],[f352,f31])).
% 0.23/0.52  fof(f352,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | (~spl2_4 | spl2_12 | ~spl2_22)),
% 0.23/0.52    inference(forward_demodulation,[],[f327,f44])).
% 0.23/0.52  fof(f327,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | (spl2_12 | ~spl2_22)),
% 0.23/0.52    inference(superposition,[],[f150,f292])).
% 0.23/0.52  fof(f292,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) ) | ~spl2_22),
% 0.23/0.52    inference(avatar_component_clause,[],[f291])).
% 0.23/0.52  fof(f150,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_12),
% 0.23/0.52    inference(avatar_component_clause,[],[f148])).
% 0.23/0.52  fof(f293,plain,(
% 0.23/0.52    spl2_22 | ~spl2_1 | ~spl2_8),
% 0.23/0.52    inference(avatar_split_clause,[],[f86,f63,f30,f291])).
% 0.23/0.52  fof(f63,plain,(
% 0.23/0.52    spl2_8 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.23/0.52  fof(f86,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) ) | (~spl2_1 | ~spl2_8)),
% 0.23/0.52    inference(superposition,[],[f64,f31])).
% 0.23/0.52  fof(f64,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_8),
% 0.23/0.52    inference(avatar_component_clause,[],[f63])).
% 0.23/0.52  fof(f155,plain,(
% 0.23/0.52    spl2_13 | ~spl2_6 | ~spl2_9),
% 0.23/0.52    inference(avatar_split_clause,[],[f111,f67,f55,f153])).
% 0.23/0.52  fof(f55,plain,(
% 0.23/0.52    spl2_6 <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.52  fof(f67,plain,(
% 0.23/0.52    spl2_9 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.23/0.52  fof(f111,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | (~spl2_6 | ~spl2_9)),
% 0.23/0.52    inference(superposition,[],[f56,f68])).
% 0.23/0.52  fof(f68,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_9),
% 0.23/0.52    inference(avatar_component_clause,[],[f67])).
% 0.23/0.52  fof(f56,plain,(
% 0.23/0.52    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | ~spl2_6),
% 0.23/0.52    inference(avatar_component_clause,[],[f55])).
% 0.23/0.52  fof(f151,plain,(
% 0.23/0.52    ~spl2_12),
% 0.23/0.52    inference(avatar_split_clause,[],[f26,f148])).
% 0.23/0.52  fof(f26,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.23/0.52    inference(definition_unfolding,[],[f16,f22,f19])).
% 0.23/0.52  fof(f19,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f8])).
% 0.23/0.52  fof(f8,axiom,(
% 0.23/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f2])).
% 0.23/0.52  fof(f2,axiom,(
% 0.23/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.23/0.52    inference(cnf_transformation,[],[f15])).
% 0.23/0.52  fof(f15,plain,(
% 0.23/0.52    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.23/0.52  fof(f14,plain,(
% 0.23/0.52    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f11])).
% 0.23/0.52  fof(f11,negated_conjecture,(
% 0.23/0.52    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.23/0.52    inference(negated_conjecture,[],[f10])).
% 0.23/0.52  fof(f10,conjecture,(
% 0.23/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.23/0.52  fof(f69,plain,(
% 0.23/0.52    spl2_9),
% 0.23/0.52    inference(avatar_split_clause,[],[f28,f67])).
% 0.23/0.52  fof(f28,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.23/0.52    inference(definition_unfolding,[],[f20,f19])).
% 0.23/0.52  fof(f20,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.23/0.52  fof(f65,plain,(
% 0.23/0.52    spl2_8),
% 0.23/0.52    inference(avatar_split_clause,[],[f25,f63])).
% 0.23/0.52  fof(f25,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f9])).
% 0.23/0.52  fof(f9,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.23/0.52  fof(f57,plain,(
% 0.23/0.52    spl2_6 | ~spl2_1 | ~spl2_5),
% 0.23/0.52    inference(avatar_split_clause,[],[f50,f47,f30,f55])).
% 0.23/0.52  fof(f47,plain,(
% 0.23/0.52    spl2_5 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.52  fof(f50,plain,(
% 0.23/0.52    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | (~spl2_1 | ~spl2_5)),
% 0.23/0.52    inference(superposition,[],[f48,f31])).
% 0.23/0.52  fof(f48,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | ~spl2_5),
% 0.23/0.52    inference(avatar_component_clause,[],[f47])).
% 0.23/0.52  fof(f49,plain,(
% 0.23/0.52    spl2_5 | ~spl2_2 | ~spl2_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f41,f38,f34,f47])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    spl2_2 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.52  fof(f38,plain,(
% 0.23/0.52    spl2_3 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.52  fof(f41,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0) ) | (~spl2_2 | ~spl2_3)),
% 0.23/0.52    inference(resolution,[],[f39,f35])).
% 0.23/0.52  fof(f35,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) ) | ~spl2_2),
% 0.23/0.52    inference(avatar_component_clause,[],[f34])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_3),
% 0.23/0.52    inference(avatar_component_clause,[],[f38])).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    spl2_4),
% 0.23/0.52    inference(avatar_split_clause,[],[f21,f43])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    spl2_3),
% 0.23/0.52    inference(avatar_split_clause,[],[f23,f38])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f13])).
% 0.23/0.52  fof(f13,plain,(
% 0.23/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f3])).
% 0.23/0.52  fof(f3,axiom,(
% 0.23/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.52  fof(f36,plain,(
% 0.23/0.52    spl2_2),
% 0.23/0.52    inference(avatar_split_clause,[],[f27,f34])).
% 0.23/0.52  fof(f27,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.23/0.52    inference(definition_unfolding,[],[f17,f19])).
% 0.23/0.52  fof(f17,plain,(
% 0.23/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f4])).
% 0.23/0.52  fof(f4,axiom,(
% 0.23/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.52  fof(f32,plain,(
% 0.23/0.52    spl2_1),
% 0.23/0.52    inference(avatar_split_clause,[],[f18,f30])).
% 0.23/0.52  fof(f18,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.52  % SZS output end Proof for theBenchmark
% 0.23/0.52  % (28406)------------------------------
% 0.23/0.52  % (28406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (28406)Termination reason: Refutation
% 0.23/0.52  
% 0.23/0.52  % (28406)Memory used [KB]: 6396
% 0.23/0.52  % (28406)Time elapsed: 0.069 s
% 0.23/0.52  % (28406)------------------------------
% 0.23/0.52  % (28406)------------------------------
% 0.23/0.53  % (28398)Success in time 0.158 s
%------------------------------------------------------------------------------
