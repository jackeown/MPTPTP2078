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
% DateTime   : Thu Dec  3 12:31:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 108 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  156 ( 260 expanded)
%              Number of equality atoms :   40 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f40,f48,f52,f56,f60,f66,f74,f92,f107,f134,f209])).

fof(f209,plain,
    ( ~ spl3_11
    | spl3_14
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl3_11
    | spl3_14
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f200,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f200,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_14
    | ~ spl3_21 ),
    inference(superposition,[],[f91,f133])).

fof(f133,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_21
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f91,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_14
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f134,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f130,f105,f38,f132])).

fof(f38,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f105,plain,
    ( spl3_16
  <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f130,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f126,f106])).

fof(f106,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f126,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(superposition,[],[f106,f39])).

fof(f39,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f107,plain,
    ( spl3_16
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f99,f63,f58,f105])).

fof(f58,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f63,plain,
    ( spl3_10
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f99,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(superposition,[],[f59,f65])).

fof(f65,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f59,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f92,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f86,f54,f23,f89])).

fof(f23,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f86,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f55,f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f74,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f69,f50,f33,f71])).

fof(f33,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f66,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f61,f46,f28,f63])).

fof(f28,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f47,f30])).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f60,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f21,f58])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f56,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f19,f54])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f52,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f46])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f36,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f33])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f31,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f23])).

fof(f15,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:48:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.40  % (6288)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.40  % (6288)Refutation found. Thanks to Tanya!
% 0.21/0.40  % SZS status Theorem for theBenchmark
% 0.21/0.40  % SZS output start Proof for theBenchmark
% 0.21/0.40  fof(f211,plain,(
% 0.21/0.40    $false),
% 0.21/0.40    inference(avatar_sat_refutation,[],[f26,f31,f36,f40,f48,f52,f56,f60,f66,f74,f92,f107,f134,f209])).
% 0.21/0.40  fof(f209,plain,(
% 0.21/0.40    ~spl3_11 | spl3_14 | ~spl3_21),
% 0.21/0.40    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.40  fof(f208,plain,(
% 0.21/0.40    $false | (~spl3_11 | spl3_14 | ~spl3_21)),
% 0.21/0.40    inference(subsumption_resolution,[],[f200,f73])).
% 0.21/0.40  fof(f73,plain,(
% 0.21/0.40    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_11),
% 0.21/0.40    inference(avatar_component_clause,[],[f71])).
% 0.21/0.40  fof(f71,plain,(
% 0.21/0.40    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.40  fof(f200,plain,(
% 0.21/0.40    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_14 | ~spl3_21)),
% 0.21/0.40    inference(superposition,[],[f91,f133])).
% 0.21/0.40  fof(f133,plain,(
% 0.21/0.40    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ) | ~spl3_21),
% 0.21/0.40    inference(avatar_component_clause,[],[f132])).
% 0.21/0.40  fof(f132,plain,(
% 0.21/0.40    spl3_21 <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.40  fof(f91,plain,(
% 0.21/0.40    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_14),
% 0.21/0.40    inference(avatar_component_clause,[],[f89])).
% 0.21/0.40  fof(f89,plain,(
% 0.21/0.40    spl3_14 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.40  fof(f134,plain,(
% 0.21/0.40    spl3_21 | ~spl3_4 | ~spl3_16),
% 0.21/0.40    inference(avatar_split_clause,[],[f130,f105,f38,f132])).
% 0.21/0.40  fof(f38,plain,(
% 0.21/0.40    spl3_4 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.40  fof(f105,plain,(
% 0.21/0.40    spl3_16 <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.40  fof(f130,plain,(
% 0.21/0.40    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ) | (~spl3_4 | ~spl3_16)),
% 0.21/0.40    inference(forward_demodulation,[],[f126,f106])).
% 0.21/0.40  fof(f106,plain,(
% 0.21/0.40    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_16),
% 0.21/0.40    inference(avatar_component_clause,[],[f105])).
% 0.21/0.40  fof(f126,plain,(
% 0.21/0.40    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ) | (~spl3_4 | ~spl3_16)),
% 0.21/0.40    inference(superposition,[],[f106,f39])).
% 0.21/0.40  fof(f39,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl3_4),
% 0.21/0.40    inference(avatar_component_clause,[],[f38])).
% 0.21/0.40  fof(f107,plain,(
% 0.21/0.40    spl3_16 | ~spl3_9 | ~spl3_10),
% 0.21/0.40    inference(avatar_split_clause,[],[f99,f63,f58,f105])).
% 0.21/0.40  fof(f58,plain,(
% 0.21/0.40    spl3_9 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.40  fof(f63,plain,(
% 0.21/0.40    spl3_10 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.40  fof(f99,plain,(
% 0.21/0.40    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) ) | (~spl3_9 | ~spl3_10)),
% 0.21/0.40    inference(superposition,[],[f59,f65])).
% 0.21/0.40  fof(f65,plain,(
% 0.21/0.40    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_10),
% 0.21/0.40    inference(avatar_component_clause,[],[f63])).
% 0.21/0.40  fof(f59,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_9),
% 0.21/0.40    inference(avatar_component_clause,[],[f58])).
% 0.21/0.40  fof(f92,plain,(
% 0.21/0.40    ~spl3_14 | spl3_1 | ~spl3_8),
% 0.21/0.40    inference(avatar_split_clause,[],[f86,f54,f23,f89])).
% 0.21/0.40  fof(f23,plain,(
% 0.21/0.40    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.40  fof(f54,plain,(
% 0.21/0.40    spl3_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.40  fof(f86,plain,(
% 0.21/0.40    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (spl3_1 | ~spl3_8)),
% 0.21/0.40    inference(resolution,[],[f55,f25])).
% 0.21/0.40  fof(f25,plain,(
% 0.21/0.40    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | spl3_1),
% 0.21/0.40    inference(avatar_component_clause,[],[f23])).
% 0.21/0.40  fof(f55,plain,(
% 0.21/0.40    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl3_8),
% 0.21/0.40    inference(avatar_component_clause,[],[f54])).
% 0.21/0.40  fof(f74,plain,(
% 0.21/0.40    spl3_11 | ~spl3_3 | ~spl3_7),
% 0.21/0.40    inference(avatar_split_clause,[],[f69,f50,f33,f71])).
% 0.21/0.40  fof(f33,plain,(
% 0.21/0.40    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.40  fof(f50,plain,(
% 0.21/0.40    spl3_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.40  fof(f69,plain,(
% 0.21/0.40    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_7)),
% 0.21/0.40    inference(resolution,[],[f51,f35])).
% 0.21/0.40  fof(f35,plain,(
% 0.21/0.40    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.40    inference(avatar_component_clause,[],[f33])).
% 0.21/0.40  fof(f51,plain,(
% 0.21/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_7),
% 0.21/0.40    inference(avatar_component_clause,[],[f50])).
% 0.21/0.40  fof(f66,plain,(
% 0.21/0.40    spl3_10 | ~spl3_2 | ~spl3_6),
% 0.21/0.40    inference(avatar_split_clause,[],[f61,f46,f28,f63])).
% 0.21/0.40  fof(f28,plain,(
% 0.21/0.40    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.40  fof(f46,plain,(
% 0.21/0.40    spl3_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.40    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.40  fof(f61,plain,(
% 0.21/0.40    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_6)),
% 0.21/0.40    inference(resolution,[],[f47,f30])).
% 0.21/0.40  fof(f30,plain,(
% 0.21/0.40    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.40    inference(avatar_component_clause,[],[f28])).
% 0.21/0.40  fof(f47,plain,(
% 0.21/0.40    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_6),
% 0.21/0.40    inference(avatar_component_clause,[],[f46])).
% 0.21/0.40  fof(f60,plain,(
% 0.21/0.40    spl3_9),
% 0.21/0.40    inference(avatar_split_clause,[],[f21,f58])).
% 0.21/0.40  fof(f21,plain,(
% 0.21/0.40    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.40    inference(cnf_transformation,[],[f3])).
% 0.21/0.40  fof(f3,axiom,(
% 0.21/0.40    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.40  fof(f56,plain,(
% 0.21/0.40    spl3_8),
% 0.21/0.40    inference(avatar_split_clause,[],[f19,f54])).
% 0.21/0.40  fof(f19,plain,(
% 0.21/0.40    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.40    inference(cnf_transformation,[],[f12])).
% 0.21/0.40  fof(f12,plain,(
% 0.21/0.40    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.40    inference(nnf_transformation,[],[f1])).
% 0.21/0.40  fof(f1,axiom,(
% 0.21/0.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.40  fof(f52,plain,(
% 0.21/0.40    spl3_7),
% 0.21/0.40    inference(avatar_split_clause,[],[f20,f50])).
% 0.21/0.40  fof(f20,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f12])).
% 0.21/0.40  fof(f48,plain,(
% 0.21/0.40    spl3_6),
% 0.21/0.40    inference(avatar_split_clause,[],[f17,f46])).
% 0.21/0.40  fof(f17,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f11])).
% 0.21/0.40  fof(f11,plain,(
% 0.21/0.40    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.40    inference(nnf_transformation,[],[f4])).
% 0.21/0.40  fof(f4,axiom,(
% 0.21/0.40    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.40  fof(f40,plain,(
% 0.21/0.40    spl3_4),
% 0.21/0.40    inference(avatar_split_clause,[],[f16,f38])).
% 0.21/0.40  fof(f16,plain,(
% 0.21/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f2])).
% 0.21/0.40  fof(f2,axiom,(
% 0.21/0.40    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.40  fof(f36,plain,(
% 0.21/0.40    spl3_3),
% 0.21/0.40    inference(avatar_split_clause,[],[f13,f33])).
% 0.21/0.40  fof(f13,plain,(
% 0.21/0.40    r1_tarski(sK0,sK1)),
% 0.21/0.40    inference(cnf_transformation,[],[f10])).
% 0.21/0.40  fof(f10,plain,(
% 0.21/0.40    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.21/0.40  fof(f9,plain,(
% 0.21/0.40    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.40    introduced(choice_axiom,[])).
% 0.21/0.40  fof(f8,plain,(
% 0.21/0.40    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 0.21/0.40    inference(flattening,[],[f7])).
% 0.21/0.40  fof(f7,plain,(
% 0.21/0.40    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.40    inference(ennf_transformation,[],[f6])).
% 0.21/0.40  fof(f6,negated_conjecture,(
% 0.21/0.40    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.40    inference(negated_conjecture,[],[f5])).
% 0.21/0.40  fof(f5,conjecture,(
% 0.21/0.40    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.40  fof(f31,plain,(
% 0.21/0.40    spl3_2),
% 0.21/0.40    inference(avatar_split_clause,[],[f14,f28])).
% 0.21/0.40  fof(f14,plain,(
% 0.21/0.40    r1_xboole_0(sK0,sK2)),
% 0.21/0.40    inference(cnf_transformation,[],[f10])).
% 0.21/0.40  fof(f26,plain,(
% 0.21/0.40    ~spl3_1),
% 0.21/0.40    inference(avatar_split_clause,[],[f15,f23])).
% 0.21/0.40  fof(f15,plain,(
% 0.21/0.40    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.40    inference(cnf_transformation,[],[f10])).
% 0.21/0.40  % SZS output end Proof for theBenchmark
% 0.21/0.40  % (6288)------------------------------
% 0.21/0.40  % (6288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.40  % (6288)Termination reason: Refutation
% 0.21/0.40  
% 0.21/0.40  % (6288)Memory used [KB]: 10618
% 0.21/0.40  % (6288)Time elapsed: 0.005 s
% 0.21/0.40  % (6288)------------------------------
% 0.21/0.40  % (6288)------------------------------
% 0.21/0.40  % (6282)Success in time 0.047 s
%------------------------------------------------------------------------------
