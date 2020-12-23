%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 115 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  178 ( 273 expanded)
%              Number of equality atoms :   58 (  99 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f42,f48,f57,f61,f69,f100,f108,f112,f179,f188])).

fof(f188,plain,
    ( spl2_1
    | ~ spl2_19 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl2_1
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f184,f181])).

fof(f181,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl2_19 ),
    inference(superposition,[],[f178,f178])).

fof(f178,plain,
    ( ! [X0] : sK1 = X0
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl2_19
  <=> ! [X0] : sK1 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f184,plain,
    ( ! [X0] : sK0 != X0
    | spl2_1
    | ~ spl2_19 ),
    inference(superposition,[],[f25,f178])).

fof(f25,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f179,plain,
    ( spl2_19
    | spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f132,f110,f106,f67,f32,f24,f177])).

fof(f32,plain,
    ( spl2_3
  <=> ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( spl2_10
  <=> ! [X0] : k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f106,plain,
    ( spl2_14
  <=> ! [X0] :
        ( r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(X0)))
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f110,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2)
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f132,plain,
    ( ! [X0] : sK1 = X0
    | spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f129,f33])).

fof(f33,plain,
    ( ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f129,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
        | sK1 = X0 )
    | spl2_1
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f107,f123])).

fof(f123,plain,
    ( ! [X0] : k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),X0)
    | spl2_1
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f117,f25])).

fof(f117,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),X0)
        | sK0 = sK1 )
    | ~ spl2_10
    | ~ spl2_15 ),
    inference(superposition,[],[f111,f68])).

fof(f68,plain,
    ( ! [X0] : k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2)
        | X0 = X1 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f107,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(X0)))
        | sK1 = X0 )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f112,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f62,f55,f40,f110])).

fof(f40,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( X0 = X1
        | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f55,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2)
        | X0 = X1 )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f108,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f103,f98,f28,f106])).

fof(f28,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f98,plain,
    ( spl2_13
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k3_xboole_0(X0,k1_tarski(X1)),k3_xboole_0(X0,k1_tarski(X2)))
        | X1 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f103,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(X0)))
        | sK1 = X0 )
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(superposition,[],[f99,f29])).

fof(f29,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k3_xboole_0(X0,k1_tarski(X1)),k3_xboole_0(X0,k1_tarski(X2)))
        | X1 = X2 )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,
    ( spl2_13
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f53,f46,f40,f98])).

fof(f46,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f53,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k3_xboole_0(X0,k1_tarski(X1)),k3_xboole_0(X0,k1_tarski(X2)))
        | X1 = X2 )
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f69,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f65,f59,f36,f28,f67])).

fof(f36,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f59,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f65,plain,
    ( ! [X0] : k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f63,f37])).

fof(f37,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f63,plain,
    ( ! [X0] : k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) = k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f60,f29])).

fof(f60,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f19,f59])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f57,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f48,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f42,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f38,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f34,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f32])).

fof(f22,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f30,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f26,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f24])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:05:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (15752)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.45  % (15744)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (15744)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f189,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f26,f30,f34,f38,f42,f48,f57,f61,f69,f100,f108,f112,f179,f188])).
% 0.20/0.46  fof(f188,plain,(
% 0.20/0.46    spl2_1 | ~spl2_19),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.46  fof(f187,plain,(
% 0.20/0.46    $false | (spl2_1 | ~spl2_19)),
% 0.20/0.46    inference(subsumption_resolution,[],[f184,f181])).
% 0.20/0.46  fof(f181,plain,(
% 0.20/0.46    ( ! [X0,X1] : (X0 = X1) ) | ~spl2_19),
% 0.20/0.46    inference(superposition,[],[f178,f178])).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    ( ! [X0] : (sK1 = X0) ) | ~spl2_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f177])).
% 0.20/0.46  fof(f177,plain,(
% 0.20/0.46    spl2_19 <=> ! [X0] : sK1 = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    ( ! [X0] : (sK0 != X0) ) | (spl2_1 | ~spl2_19)),
% 0.20/0.46    inference(superposition,[],[f25,f178])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    sK0 != sK1 | spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    spl2_1 <=> sK0 = sK1),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f179,plain,(
% 0.20/0.46    spl2_19 | spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_14 | ~spl2_15),
% 0.20/0.46    inference(avatar_split_clause,[],[f132,f110,f106,f67,f32,f24,f177])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl2_3 <=> ! [X1] : ~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl2_10 <=> ! [X0] : k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    spl2_14 <=> ! [X0] : (r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(X0))) | sK1 = X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    spl2_15 <=> ! [X1,X0,X2] : (k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2) | X0 = X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    ( ! [X0] : (sK1 = X0) ) | (spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_14 | ~spl2_15)),
% 0.20/0.46    inference(subsumption_resolution,[],[f129,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) ) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f32])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | sK1 = X0) ) | (spl2_1 | ~spl2_10 | ~spl2_14 | ~spl2_15)),
% 0.20/0.46    inference(backward_demodulation,[],[f107,f123])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),X0)) ) | (spl2_1 | ~spl2_10 | ~spl2_15)),
% 0.20/0.46    inference(subsumption_resolution,[],[f117,f25])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),X0) | sK0 = sK1) ) | (~spl2_10 | ~spl2_15)),
% 0.20/0.46    inference(superposition,[],[f111,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))) ) | ~spl2_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2) | X0 = X1) ) | ~spl2_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f110])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(X0))) | sK1 = X0) ) | ~spl2_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f106])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    spl2_15 | ~spl2_5 | ~spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f62,f55,f40,f110])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl2_5 <=> ! [X1,X0] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl2_8 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k1_tarski(X0),X2) | X0 = X1) ) | (~spl2_5 | ~spl2_8)),
% 0.20/0.46    inference(resolution,[],[f56,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) ) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f40])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) ) | ~spl2_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f55])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    spl2_14 | ~spl2_2 | ~spl2_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f103,f98,f28,f106])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    spl2_2 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    spl2_13 <=> ! [X1,X0,X2] : (r1_xboole_0(k3_xboole_0(X0,k1_tarski(X1)),k3_xboole_0(X0,k1_tarski(X2))) | X1 = X2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(X0))) | sK1 = X0) ) | (~spl2_2 | ~spl2_13)),
% 0.20/0.46    inference(superposition,[],[f99,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f28])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k1_tarski(X1)),k3_xboole_0(X0,k1_tarski(X2))) | X1 = X2) ) | ~spl2_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f98])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    spl2_13 | ~spl2_5 | ~spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f53,f46,f40,f98])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl2_6 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k1_tarski(X1)),k3_xboole_0(X0,k1_tarski(X2))) | X1 = X2) ) | (~spl2_5 | ~spl2_6)),
% 0.20/0.46    inference(resolution,[],[f47,f41])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))) ) | ~spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl2_10 | ~spl2_2 | ~spl2_4 | ~spl2_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f65,f59,f36,f28,f67])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl2_9 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X0] : (k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))) ) | (~spl2_2 | ~spl2_4 | ~spl2_9)),
% 0.20/0.46    inference(forward_demodulation,[],[f63,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f36])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X0] : (k3_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0)) = k2_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X0))) ) | (~spl2_2 | ~spl2_9)),
% 0.20/0.46    inference(superposition,[],[f60,f29])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl2_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl2_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f59])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f55])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f46])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f40])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f36])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f32])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.46    inference(equality_resolution,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f28])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f15,f24])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    sK0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (15744)------------------------------
% 0.20/0.46  % (15744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15744)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (15744)Memory used [KB]: 10618
% 0.20/0.46  % (15744)Time elapsed: 0.049 s
% 0.20/0.46  % (15744)------------------------------
% 0.20/0.46  % (15744)------------------------------
% 0.20/0.46  % (15748)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (15743)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (15734)Success in time 0.115 s
%------------------------------------------------------------------------------
