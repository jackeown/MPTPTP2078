%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 111 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 188 expanded)
%              Number of equality atoms :   29 (  66 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f63,f84,f255,f368,f392])).

fof(f392,plain,
    ( spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f391,f365,f81])).

fof(f81,plain,
    ( spl3_6
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f365,plain,
    ( spl3_9
  <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f391,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f382,f93])).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f382,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)))
    | ~ spl3_9 ),
    inference(resolution,[],[f367,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f367,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f365])).

fof(f368,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f340,f59,f365])).

fof(f59,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f340,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_4 ),
    inference(superposition,[],[f323,f61])).

fof(f61,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f323,plain,(
    ! [X6,X7,X5] : r1_tarski(k3_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X7))),k3_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f98,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f35,f29])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f28,f24,f24])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f98,plain,(
    ! [X6,X7,X5] : r1_tarski(k5_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,k3_xboole_0(X6,X7))),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f255,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f249,f59,f41])).

fof(f41,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f249,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f209,f61])).

fof(f209,plain,(
    ! [X10,X8,X9] : r1_xboole_0(k3_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X10))),X10) ),
    inference(forward_demodulation,[],[f99,f103])).

fof(f99,plain,(
    ! [X10,X8,X9] : r1_xboole_0(k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X8,k3_xboole_0(X9,X10))),X10) ),
    inference(superposition,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f84,plain,
    ( ~ spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f78,f37,f81])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f78,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f39,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f63,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f56,f46,f59])).

fof(f46,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f56,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f25,f48])).

fof(f48,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f18,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f41,f37])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:58:02 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (32522)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.45  % (32522)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.46  % (32517)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f394,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f44,f49,f63,f84,f255,f368,f392])).
% 0.22/0.46  fof(f392,plain,(
% 0.22/0.46    spl3_6 | ~spl3_9),
% 0.22/0.46    inference(avatar_split_clause,[],[f391,f365,f81])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    spl3_6 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.46  fof(f365,plain,(
% 0.22/0.46    spl3_9 <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.46  fof(f391,plain,(
% 0.22/0.46    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_9),
% 0.22/0.46    inference(forward_demodulation,[],[f382,f93])).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(superposition,[],[f29,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.46    inference(rectify,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.46  fof(f382,plain,(
% 0.22/0.46    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))) | ~spl3_9),
% 0.22/0.46    inference(resolution,[],[f367,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f27,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.46    inference(nnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.46  fof(f367,plain,(
% 0.22/0.46    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f365])).
% 0.22/0.46  fof(f368,plain,(
% 0.22/0.46    spl3_9 | ~spl3_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f340,f59,f365])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    spl3_4 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.46  fof(f340,plain,(
% 0.22/0.46    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_4),
% 0.22/0.46    inference(superposition,[],[f323,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f59])).
% 0.22/0.46  fof(f323,plain,(
% 0.22/0.46    ( ! [X6,X7,X5] : (r1_tarski(k3_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X7))),k3_xboole_0(X5,X6))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f98,f103])).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f35,f29])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f28,f24,f24])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    ( ! [X6,X7,X5] : (r1_tarski(k5_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X5,k3_xboole_0(X6,X7))),k3_xboole_0(X5,X6))) )),
% 0.22/0.46    inference(superposition,[],[f32,f29])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f23,f24])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.46  fof(f255,plain,(
% 0.22/0.46    spl3_2 | ~spl3_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f249,f59,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.46  fof(f249,plain,(
% 0.22/0.46    r1_xboole_0(sK0,sK2) | ~spl3_4),
% 0.22/0.46    inference(superposition,[],[f209,f61])).
% 0.22/0.46  fof(f209,plain,(
% 0.22/0.46    ( ! [X10,X8,X9] : (r1_xboole_0(k3_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X10))),X10)) )),
% 0.22/0.46    inference(forward_demodulation,[],[f99,f103])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    ( ! [X10,X8,X9] : (r1_xboole_0(k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X8,k3_xboole_0(X9,X10))),X10)) )),
% 0.22/0.46    inference(superposition,[],[f31,f29])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f22,f24])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    ~spl3_6 | spl3_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f78,f37,f81])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.46  fof(f78,plain,(
% 0.22/0.46    k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl3_1),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f39,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f26,f24])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f37])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    spl3_4 | ~spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f56,f46,f59])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.46    inference(resolution,[],[f25,f48])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f46])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f30,f46])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.46    inference(definition_unfolding,[],[f18,f24])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.46    inference(ennf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.46    inference(negated_conjecture,[],[f10])).
% 0.22/0.46  fof(f10,conjecture,(
% 0.22/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    ~spl3_1 | ~spl3_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f19,f41,f37])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f16])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (32522)------------------------------
% 0.22/0.46  % (32522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (32522)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (32522)Memory used [KB]: 6268
% 0.22/0.46  % (32522)Time elapsed: 0.060 s
% 0.22/0.46  % (32522)------------------------------
% 0.22/0.46  % (32522)------------------------------
% 0.22/0.46  % (32515)Success in time 0.1 s
%------------------------------------------------------------------------------
