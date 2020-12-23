%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 528 expanded)
%              Number of leaves         :   15 ( 181 expanded)
%              Depth                    :   17
%              Number of atoms          :  126 ( 599 expanded)
%              Number of equality atoms :   77 ( 527 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f863,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f81,f835,f861])).

fof(f861,plain,
    ( ~ spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | ~ spl2_1
    | spl2_3 ),
    inference(subsumption_resolution,[],[f859,f79])).

fof(f79,plain,
    ( k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_3
  <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f859,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f852,f798])).

fof(f798,plain,(
    ! [X14,X13] : k4_xboole_0(X14,k4_xboole_0(X13,X13)) = X14 ),
    inference(forward_demodulation,[],[f797,f663])).

fof(f663,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6 ),
    inference(superposition,[],[f82,f281])).

fof(f281,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4 ),
    inference(backward_demodulation,[],[f126,f278])).

fof(f278,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(backward_demodulation,[],[f211,f266])).

fof(f266,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,X8),X9)) ),
    inference(superposition,[],[f44,f67])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f49,f31])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f211,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),X3)) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f55,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f52,f44])).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f42,f34,f34])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f126,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4 ),
    inference(superposition,[],[f50,f48])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

% (6980)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f797,plain,(
    ! [X14,X13] : k4_xboole_0(X14,k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X13))) = X14 ),
    inference(forward_demodulation,[],[f796,f626])).

fof(f626,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X30,k2_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X29,k4_xboole_0(X29,X28)))) = k4_xboole_0(X30,k2_xboole_0(k4_xboole_0(X30,X28),X29)) ),
    inference(forward_demodulation,[],[f600,f55])).

fof(f600,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X30,k2_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X29,k4_xboole_0(X29,X28)))) = k4_xboole_0(X30,k4_xboole_0(X30,k4_xboole_0(X28,X29))) ),
    inference(superposition,[],[f55,f278])).

fof(f796,plain,(
    ! [X14,X13] : k4_xboole_0(X14,k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X14))))) = X14 ),
    inference(forward_demodulation,[],[f770,f44])).

fof(f770,plain,(
    ! [X14,X13] : k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,X14)))) = X14 ),
    inference(superposition,[],[f375,f121])).

fof(f121,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f50,f48])).

fof(f375,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X2)) ),
    inference(backward_demodulation,[],[f86,f374])).

fof(f374,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,X3) = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f360,f335])).

fof(f335,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f331,f291])).

fof(f291,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f210,f288])).

fof(f288,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f43,f125])).

fof(f125,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2 ),
    inference(superposition,[],[f50,f49])).

fof(f210,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f55,f49])).

fof(f331,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f35,f82])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f360,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f291,f43])).

fof(f86,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,k2_xboole_0(X3,X4)))) ),
    inference(superposition,[],[f49,f43])).

fof(f852,plain,
    ( k4_xboole_0(k1_tarski(sK1),sK0) = k4_xboole_0(k1_tarski(sK1),k4_xboole_0(sK0,sK0))
    | ~ spl2_1 ),
    inference(superposition,[],[f278,f61])).

fof(f61,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_1
  <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f835,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f834])).

fof(f834,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f135,f831])).

fof(f831,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f30,f800])).

fof(f800,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f581,f798])).

fof(f581,plain,
    ( k4_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(sK0,k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)))
    | ~ spl2_3 ),
    inference(superposition,[],[f278,f80])).

fof(f80,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f30,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f135,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f80,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f81,plain,
    ( spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f71,f63,f78])).

fof(f63,plain,
    ( spl2_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f71,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0)
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f65,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f66,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f29,f63,f59])).

fof(f29,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (6994)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (6983)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (6981)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (6994)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f863,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f66,f81,f835,f861])).
% 0.21/0.47  fof(f861,plain,(
% 0.21/0.47    ~spl2_1 | spl2_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f860])).
% 0.21/0.47  fof(f860,plain,(
% 0.21/0.47    $false | (~spl2_1 | spl2_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f859,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK0) | spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl2_3 <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f859,plain,(
% 0.21/0.47    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0) | ~spl2_1),
% 0.21/0.47    inference(forward_demodulation,[],[f852,f798])).
% 0.21/0.47  fof(f798,plain,(
% 0.21/0.47    ( ! [X14,X13] : (k4_xboole_0(X14,k4_xboole_0(X13,X13)) = X14) )),
% 0.21/0.47    inference(forward_demodulation,[],[f797,f663])).
% 0.21/0.47  fof(f663,plain,(
% 0.21/0.47    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X7),X6) = X6) )),
% 0.21/0.47    inference(superposition,[],[f82,f281])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4) )),
% 0.21/0.47    inference(backward_demodulation,[],[f126,f278])).
% 0.21/0.47  fof(f278,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f211,f266])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(k4_xboole_0(X8,X8),X9))) )),
% 0.21/0.47    inference(superposition,[],[f44,f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.47    inference(superposition,[],[f49,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    inference(rectify,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f33,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),X3)) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 0.21/0.47    inference(superposition,[],[f55,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f32,f34,f34])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f52,f44])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f34,f34])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))),k4_xboole_0(X5,k4_xboole_0(X5,X4))) = X4) )),
% 0.21/0.47    inference(superposition,[],[f50,f48])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f36,f34])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.47  % (6980)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(superposition,[],[f43,f31])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.47  fof(f797,plain,(
% 0.21/0.47    ( ! [X14,X13] : (k4_xboole_0(X14,k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),X13))) = X14) )),
% 0.21/0.47    inference(forward_demodulation,[],[f796,f626])).
% 0.21/0.47  fof(f626,plain,(
% 0.21/0.47    ( ! [X30,X28,X29] : (k4_xboole_0(X30,k2_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X29,k4_xboole_0(X29,X28)))) = k4_xboole_0(X30,k2_xboole_0(k4_xboole_0(X30,X28),X29))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f600,f55])).
% 0.21/0.47  fof(f600,plain,(
% 0.21/0.47    ( ! [X30,X28,X29] : (k4_xboole_0(X30,k2_xboole_0(k4_xboole_0(X30,X28),k4_xboole_0(X29,k4_xboole_0(X29,X28)))) = k4_xboole_0(X30,k4_xboole_0(X30,k4_xboole_0(X28,X29)))) )),
% 0.21/0.47    inference(superposition,[],[f55,f278])).
% 0.21/0.47  fof(f796,plain,(
% 0.21/0.47    ( ! [X14,X13] : (k4_xboole_0(X14,k4_xboole_0(X13,k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X13,k4_xboole_0(X13,X14))))) = X14) )),
% 0.21/0.47    inference(forward_demodulation,[],[f770,f44])).
% 0.21/0.47  fof(f770,plain,(
% 0.21/0.47    ( ! [X14,X13] : (k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,X14)))) = X14) )),
% 0.21/0.47    inference(superposition,[],[f375,f121])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,X3)) = X2) )),
% 0.21/0.47    inference(superposition,[],[f50,f48])).
% 0.21/0.47  fof(f375,plain,(
% 0.21/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X2))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f86,f374])).
% 0.21/0.47  fof(f374,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k4_xboole_0(X3,X3) = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f360,f335])).
% 0.21/0.47  fof(f335,plain,(
% 0.21/0.47    ( ! [X6,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f331,f291])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f210,f288])).
% 0.21/0.47  fof(f288,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(superposition,[],[f43,f125])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,X2),X2) = X2) )),
% 0.21/0.47    inference(superposition,[],[f50,f49])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)))) )),
% 0.21/0.47    inference(superposition,[],[f55,f49])).
% 0.21/0.47  fof(f331,plain,(
% 0.21/0.47    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 0.21/0.47    inference(superposition,[],[f35,f82])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.47  fof(f360,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 0.21/0.47    inference(superposition,[],[f291,f43])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (k2_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,k2_xboole_0(X3,X4))))) )),
% 0.21/0.47    inference(superposition,[],[f49,f43])).
% 0.21/0.47  fof(f852,plain,(
% 0.21/0.47    k4_xboole_0(k1_tarski(sK1),sK0) = k4_xboole_0(k1_tarski(sK1),k4_xboole_0(sK0,sK0)) | ~spl2_1),
% 0.21/0.47    inference(superposition,[],[f278,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl2_1 <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f835,plain,(
% 0.21/0.47    ~spl2_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f834])).
% 0.21/0.47  fof(f834,plain,(
% 0.21/0.47    $false | ~spl2_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f135,f831])).
% 0.21/0.47  fof(f831,plain,(
% 0.21/0.47    r2_hidden(sK1,sK0) | ~spl2_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f30,f800])).
% 0.21/0.47  fof(f800,plain,(
% 0.21/0.47    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl2_3),
% 0.21/0.47    inference(backward_demodulation,[],[f581,f798])).
% 0.21/0.47  fof(f581,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(sK0,k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))) | ~spl2_3),
% 0.21/0.47    inference(superposition,[],[f278,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f17])).
% 0.21/0.48  fof(f17,conjecture,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0) | ~spl2_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f80,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl2_3 | spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f71,f63,f78])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl2_2 <=> r2_hidden(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0) | spl2_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f65,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0) | spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_1 | ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f63,f59])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6994)------------------------------
% 0.21/0.48  % (6994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6994)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6994)Memory used [KB]: 11513
% 0.21/0.48  % (6994)Time elapsed: 0.039 s
% 0.21/0.48  % (6994)------------------------------
% 0.21/0.48  % (6994)------------------------------
% 0.21/0.48  % (6975)Success in time 0.111 s
%------------------------------------------------------------------------------
