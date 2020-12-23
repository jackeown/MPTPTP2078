%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 108 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :  161 ( 225 expanded)
%              Number of equality atoms :   59 (  88 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f54,f62,f66,f70,f86,f90,f99,f111,f118,f166,f189,f231,f357])).

fof(f357,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_21
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_21
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f49,f355])).

fof(f355,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_21
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f353,f284])).

fof(f284,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f232,f53])).

fof(f53,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f232,plain,
    ( ! [X0,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,X0))
    | ~ spl2_21
    | ~ spl2_26 ),
    inference(superposition,[],[f230,f165])).

fof(f165,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl2_21
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f230,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl2_26
  <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f353,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl2_11
    | ~ spl2_24 ),
    inference(superposition,[],[f89,f188])).

fof(f188,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl2_24
  <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f89,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_11
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f49,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_2
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f231,plain,
    ( spl2_26
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f129,f109,f60,f229])).

fof(f60,plain,
    ( spl2_5
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f109,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f129,plain,
    ( ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(superposition,[],[f110,f61])).

fof(f61,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f110,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f189,plain,
    ( spl2_24
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f153,f115,f84,f186])).

fof(f84,plain,
    ( spl2_10
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f115,plain,
    ( spl2_16
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f153,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_10
    | ~ spl2_16 ),
    inference(superposition,[],[f85,f117])).

fof(f117,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f115])).

fof(f85,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f166,plain,
    ( spl2_21
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f105,f84,f68,f64,f164])).

fof(f64,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f68,plain,
    ( spl2_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f105,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f104,f69])).

fof(f69,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f104,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(superposition,[],[f85,f65])).

fof(f65,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f118,plain,
    ( spl2_16
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f112,f97,f42,f115])).

fof(f42,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f97,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f112,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f44,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f111,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f36,f109])).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f99,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f34,f97])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f90,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f86,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f32,f84])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f66,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f62,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f54,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f50,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:10:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19813)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (19811)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (19813)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f358,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f45,f50,f54,f62,f66,f70,f86,f90,f99,f111,f118,f166,f189,f231,f357])).
% 0.22/0.47  fof(f357,plain,(
% 0.22/0.47    spl2_2 | ~spl2_3 | ~spl2_11 | ~spl2_21 | ~spl2_24 | ~spl2_26),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f356])).
% 0.22/0.47  fof(f356,plain,(
% 0.22/0.47    $false | (spl2_2 | ~spl2_3 | ~spl2_11 | ~spl2_21 | ~spl2_24 | ~spl2_26)),
% 0.22/0.47    inference(subsumption_resolution,[],[f49,f355])).
% 0.22/0.47  fof(f355,plain,(
% 0.22/0.47    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | (~spl2_3 | ~spl2_11 | ~spl2_21 | ~spl2_24 | ~spl2_26)),
% 0.22/0.47    inference(forward_demodulation,[],[f353,f284])).
% 0.22/0.47  fof(f284,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1) ) | (~spl2_3 | ~spl2_21 | ~spl2_26)),
% 0.22/0.47    inference(forward_demodulation,[],[f232,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f232,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,X0))) ) | (~spl2_21 | ~spl2_26)),
% 0.22/0.47    inference(superposition,[],[f230,f165])).
% 0.22/0.47  fof(f165,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_21),
% 0.22/0.47    inference(avatar_component_clause,[],[f164])).
% 0.22/0.47  fof(f164,plain,(
% 0.22/0.47    spl2_21 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.47  fof(f230,plain,(
% 0.22/0.47    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) ) | ~spl2_26),
% 0.22/0.47    inference(avatar_component_clause,[],[f229])).
% 0.22/0.47  fof(f229,plain,(
% 0.22/0.47    spl2_26 <=> ! [X3,X5,X4] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.47  fof(f353,plain,(
% 0.22/0.47    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) | (~spl2_11 | ~spl2_24)),
% 0.22/0.47    inference(superposition,[],[f89,f188])).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) | ~spl2_24),
% 0.22/0.47    inference(avatar_component_clause,[],[f186])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    spl2_24 <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f88])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl2_11 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl2_2 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f231,plain,(
% 0.22/0.47    spl2_26 | ~spl2_5 | ~spl2_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f129,f109,f60,f229])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl2_5 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    spl2_15 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) ) | (~spl2_5 | ~spl2_15)),
% 0.22/0.47    inference(superposition,[],[f110,f61])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f60])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f109])).
% 0.22/0.47  fof(f189,plain,(
% 0.22/0.47    spl2_24 | ~spl2_10 | ~spl2_16),
% 0.22/0.47    inference(avatar_split_clause,[],[f153,f115,f84,f186])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    spl2_10 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    spl2_16 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_10 | ~spl2_16)),
% 0.22/0.47    inference(superposition,[],[f85,f117])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl2_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f115])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f84])).
% 0.22/0.47  fof(f166,plain,(
% 0.22/0.47    spl2_21 | ~spl2_6 | ~spl2_7 | ~spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f105,f84,f68,f64,f164])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    spl2_7 <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_7 | ~spl2_10)),
% 0.22/0.47    inference(forward_demodulation,[],[f104,f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) ) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f68])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_10)),
% 0.22/0.47    inference(superposition,[],[f85,f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f64])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    spl2_16 | ~spl2_1 | ~spl2_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f112,f97,f42,f115])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    spl2_13 <=> ! [X1,X0] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_1 | ~spl2_13)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f44,f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) ) | ~spl2_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f97])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f42])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    spl2_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f36,f109])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl2_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f34,f97])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl2_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f33,f88])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl2_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f32,f84])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f68])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f64])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f27,f60])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f52])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ~spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f47])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.47    inference(negated_conjecture,[],[f17])).
% 0.22/0.47  fof(f17,conjecture,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f42])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    r2_hidden(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (19813)------------------------------
% 0.22/0.47  % (19813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19808)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (19813)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (19813)Memory used [KB]: 6524
% 0.22/0.47  % (19813)Time elapsed: 0.017 s
% 0.22/0.47  % (19813)------------------------------
% 0.22/0.47  % (19813)------------------------------
% 0.22/0.48  % (19804)Success in time 0.112 s
%------------------------------------------------------------------------------
