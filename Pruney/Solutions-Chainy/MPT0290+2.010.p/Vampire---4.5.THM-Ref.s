%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :  115 ( 156 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f55,f70,f74,f101,f105,f111,f113])).

fof(f113,plain,
    ( ~ spl2_6
    | spl2_14
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl2_6
    | spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f106,f110])).

fof(f110,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl2_15
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f106,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl2_6
    | spl2_14 ),
    inference(unit_resulting_resolution,[],[f100,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f100,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_14
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f111,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f88,f68,f37,f109])).

fof(f37,plain,
    ( spl2_2
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f68,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f88,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f86,f38])).

fof(f38,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f86,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f69,f38])).

fof(f69,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f105,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_6
    | spl2_13 ),
    inference(unit_resulting_resolution,[],[f42,f96,f54])).

fof(f96,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_13
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f42,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f101,plain,
    ( ~ spl2_13
    | ~ spl2_14
    | spl2_1
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f92,f72,f32,f98,f94])).

fof(f32,plain,
    ( spl2_1
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f72,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f92,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))
    | spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f70,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f55,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (2873)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (2873)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f35,f39,f43,f55,f70,f74,f101,f105,f111,f113])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    ~spl2_6 | spl2_14 | ~spl2_15),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    $false | (~spl2_6 | spl2_14 | ~spl2_15)),
% 0.21/0.44    inference(subsumption_resolution,[],[f106,f110])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) ) | ~spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f109])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    spl2_15 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | (~spl2_6 | spl2_14)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f100,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f53])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl2_6 <=> ! [X1,X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) | spl2_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f98])).
% 0.21/0.44  fof(f98,plain,(
% 0.21/0.44    spl2_14 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    spl2_15 | ~spl2_2 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f88,f68,f37,f109])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl2_2 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl2_9 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) ) | (~spl2_2 | ~spl2_9)),
% 0.21/0.44    inference(forward_demodulation,[],[f86,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f37])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1))) ) | (~spl2_2 | ~spl2_9)),
% 0.21/0.44    inference(superposition,[],[f69,f38])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    ~spl2_3 | ~spl2_6 | spl2_13),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    $false | (~spl2_3 | ~spl2_6 | spl2_13)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f42,f96,f54])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) | spl2_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f94])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl2_13 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl2_3 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ~spl2_13 | ~spl2_14 | spl2_1 | ~spl2_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f92,f72,f32,f98,f94])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl2_1 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) | ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) | (spl2_1 | ~spl2_10)),
% 0.21/0.44    inference(resolution,[],[f73,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl2_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f29,f72])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f68])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f41])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f37])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.44    inference(rectify,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f32])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) => ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f11])).
% 0.21/0.44  fof(f11,conjecture,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (2873)------------------------------
% 0.21/0.44  % (2873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (2873)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (2873)Memory used [KB]: 6140
% 0.21/0.44  % (2873)Time elapsed: 0.009 s
% 0.21/0.44  % (2873)------------------------------
% 0.21/0.44  % (2873)------------------------------
% 0.21/0.45  % (2865)Success in time 0.089 s
%------------------------------------------------------------------------------
