%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 106 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  123 ( 187 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f75,f91,f142,f251,f634,f719,f728])).

fof(f728,plain,
    ( spl3_2
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | spl3_2
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f30,f41,f718])).

fof(f718,plain,
    ( ! [X14] :
        ( r1_tarski(X14,sK1)
        | ~ r1_tarski(X14,sK0) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl3_25
  <=> ! [X14] :
        ( ~ r1_tarski(X14,sK0)
        | r1_tarski(X14,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f41,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f719,plain,
    ( spl3_25
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f705,f632,f717])).

fof(f632,plain,
    ( spl3_23
  <=> ! [X20] :
        ( ~ r1_tarski(X20,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
        | r1_tarski(X20,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f705,plain,
    ( ! [X14] :
        ( ~ r1_tarski(X14,sK0)
        | r1_tarski(X14,sK1) )
    | ~ spl3_23 ),
    inference(superposition,[],[f633,f678])).

fof(f678,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f674,f23])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f674,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f652,f43])).

fof(f43,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f23,f20])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f652,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f633,plain,
    ( ! [X20] :
        ( ~ r1_tarski(X20,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
        | r1_tarski(X20,sK1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f632])).

fof(f634,plain,
    ( spl3_23
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f472,f248,f632])).

fof(f248,plain,
    ( spl3_16
  <=> k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f472,plain,
    ( ! [X20] :
        ( ~ r1_tarski(X20,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
        | r1_tarski(X20,sK1) )
    | ~ spl3_16 ),
    inference(superposition,[],[f32,f250])).

fof(f250,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f248])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f251,plain,
    ( spl3_16
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f143,f139,f248])).

fof(f139,plain,
    ( spl3_11
  <=> k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f143,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_11 ),
    inference(superposition,[],[f141,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f141,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f142,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f92,f88,f139])).

fof(f88,plain,
    ( spl3_5
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f90,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f90,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f91,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f78,f72,f88])).

fof(f72,plain,
    ( spl3_3
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f78,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f76,f23])).

fof(f76,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK0),sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f51,f74])).

fof(f74,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f30,f22])).

fof(f75,plain,
    ( spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f61,f34,f72])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f36,f25])).

fof(f36,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f42,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f29,f39])).

fof(f29,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f18,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:35:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.42  % (16455)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.43  % (16461)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.44  % (16461)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f729,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f37,f42,f75,f91,f142,f251,f634,f719,f728])).
% 0.19/0.44  fof(f728,plain,(
% 0.19/0.44    spl3_2 | ~spl3_25),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f725])).
% 0.19/0.44  fof(f725,plain,(
% 0.19/0.44    $false | (spl3_2 | ~spl3_25)),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f30,f41,f718])).
% 0.19/0.44  fof(f718,plain,(
% 0.19/0.44    ( ! [X14] : (r1_tarski(X14,sK1) | ~r1_tarski(X14,sK0)) ) | ~spl3_25),
% 0.19/0.44    inference(avatar_component_clause,[],[f717])).
% 0.19/0.44  fof(f717,plain,(
% 0.19/0.44    spl3_25 <=> ! [X14] : (~r1_tarski(X14,sK0) | r1_tarski(X14,sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.19/0.44  fof(f41,plain,(
% 0.19/0.44    ~r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | spl3_2),
% 0.19/0.44    inference(avatar_component_clause,[],[f39])).
% 0.19/0.44  fof(f39,plain,(
% 0.19/0.44    spl3_2 <=> r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f21,f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,axiom,(
% 0.19/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.44  fof(f719,plain,(
% 0.19/0.44    spl3_25 | ~spl3_23),
% 0.19/0.44    inference(avatar_split_clause,[],[f705,f632,f717])).
% 0.19/0.44  fof(f632,plain,(
% 0.19/0.44    spl3_23 <=> ! [X20] : (~r1_tarski(X20,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | r1_tarski(X20,sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.19/0.44  fof(f705,plain,(
% 0.19/0.44    ( ! [X14] : (~r1_tarski(X14,sK0) | r1_tarski(X14,sK1)) ) | ~spl3_23),
% 0.19/0.44    inference(superposition,[],[f633,f678])).
% 0.19/0.44  fof(f678,plain,(
% 0.19/0.44    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.19/0.44    inference(superposition,[],[f674,f23])).
% 0.19/0.44  fof(f23,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.19/0.44  fof(f674,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.19/0.44    inference(forward_demodulation,[],[f652,f43])).
% 0.19/0.44  fof(f43,plain,(
% 0.19/0.44    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.19/0.44    inference(superposition,[],[f23,f20])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f7])).
% 0.19/0.44  fof(f7,axiom,(
% 0.19/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.19/0.44  fof(f652,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.19/0.44    inference(superposition,[],[f26,f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,axiom,(
% 0.19/0.44    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.19/0.44  fof(f26,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.19/0.44  fof(f633,plain,(
% 0.19/0.44    ( ! [X20] : (~r1_tarski(X20,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | r1_tarski(X20,sK1)) ) | ~spl3_23),
% 0.19/0.44    inference(avatar_component_clause,[],[f632])).
% 0.19/0.44  fof(f634,plain,(
% 0.19/0.44    spl3_23 | ~spl3_16),
% 0.19/0.44    inference(avatar_split_clause,[],[f472,f248,f632])).
% 0.19/0.44  fof(f248,plain,(
% 0.19/0.44    spl3_16 <=> k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.44  fof(f472,plain,(
% 0.19/0.44    ( ! [X20] : (~r1_tarski(X20,k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | r1_tarski(X20,sK1)) ) | ~spl3_16),
% 0.19/0.44    inference(superposition,[],[f32,f250])).
% 0.19/0.44  fof(f250,plain,(
% 0.19/0.44    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_16),
% 0.19/0.44    inference(avatar_component_clause,[],[f248])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f27,f24])).
% 0.19/0.44  fof(f27,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.44    inference(ennf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.19/0.44  fof(f251,plain,(
% 0.19/0.44    spl3_16 | ~spl3_11),
% 0.19/0.44    inference(avatar_split_clause,[],[f143,f139,f248])).
% 0.19/0.44  fof(f139,plain,(
% 0.19/0.44    spl3_11 <=> k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.44  fof(f143,plain,(
% 0.19/0.44    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~spl3_11),
% 0.19/0.44    inference(superposition,[],[f141,f22])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.44  fof(f141,plain,(
% 0.19/0.44    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl3_11),
% 0.19/0.44    inference(avatar_component_clause,[],[f139])).
% 0.19/0.44  fof(f142,plain,(
% 0.19/0.44    spl3_11 | ~spl3_5),
% 0.19/0.44    inference(avatar_split_clause,[],[f92,f88,f139])).
% 0.19/0.44  fof(f88,plain,(
% 0.19/0.44    spl3_5 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.44  fof(f92,plain,(
% 0.19/0.44    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) | ~spl3_5),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f90,f25])).
% 0.19/0.44  fof(f25,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.44    inference(cnf_transformation,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f5])).
% 0.19/0.44  fof(f5,axiom,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.44  fof(f90,plain,(
% 0.19/0.44    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | ~spl3_5),
% 0.19/0.44    inference(avatar_component_clause,[],[f88])).
% 0.19/0.44  fof(f91,plain,(
% 0.19/0.44    spl3_5 | ~spl3_3),
% 0.19/0.44    inference(avatar_split_clause,[],[f78,f72,f88])).
% 0.19/0.44  fof(f72,plain,(
% 0.19/0.44    spl3_3 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.44  fof(f78,plain,(
% 0.19/0.44    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | ~spl3_3),
% 0.19/0.44    inference(forward_demodulation,[],[f76,f23])).
% 0.19/0.44  fof(f76,plain,(
% 0.19/0.44    r1_tarski(k5_xboole_0(sK1,sK0),sK1) | ~spl3_3),
% 0.19/0.44    inference(superposition,[],[f51,f74])).
% 0.19/0.44  fof(f74,plain,(
% 0.19/0.44    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_3),
% 0.19/0.44    inference(avatar_component_clause,[],[f72])).
% 0.19/0.44  fof(f51,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 0.19/0.44    inference(superposition,[],[f30,f22])).
% 0.19/0.44  fof(f75,plain,(
% 0.19/0.44    spl3_3 | ~spl3_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f61,f34,f72])).
% 0.19/0.44  fof(f34,plain,(
% 0.19/0.44    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.44  fof(f61,plain,(
% 0.19/0.44    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_1),
% 0.19/0.44    inference(unit_resulting_resolution,[],[f36,f25])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.19/0.44    inference(avatar_component_clause,[],[f34])).
% 0.19/0.44  fof(f42,plain,(
% 0.19/0.44    ~spl3_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f29,f39])).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ~r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 0.19/0.44    inference(definition_unfolding,[],[f18,f24])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f11])).
% 0.19/0.44  fof(f11,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.19/0.44    inference(negated_conjecture,[],[f10])).
% 0.19/0.44  fof(f10,conjecture,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.19/0.44  fof(f37,plain,(
% 0.19/0.44    spl3_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f17,f34])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    r1_tarski(sK0,sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f16])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (16461)------------------------------
% 0.19/0.44  % (16461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (16461)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (16461)Memory used [KB]: 11001
% 0.19/0.44  % (16461)Time elapsed: 0.047 s
% 0.19/0.44  % (16461)------------------------------
% 0.19/0.44  % (16461)------------------------------
% 0.19/0.45  % (16443)Success in time 0.1 s
%------------------------------------------------------------------------------
