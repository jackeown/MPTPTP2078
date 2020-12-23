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
% DateTime   : Thu Dec  3 12:43:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 114 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  169 ( 307 expanded)
%              Number of equality atoms :   58 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f51,f55,f63,f79,f84,f101,f134,f564,f594,f621])).

fof(f621,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_30
    | ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | ~ spl4_3
    | spl4_4
    | ~ spl4_30
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f46,f619])).

fof(f619,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,sK2)
    | ~ spl4_3
    | ~ spl4_30
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f595,f563])).

fof(f563,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl4_30
  <=> k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f595,plain,
    ( k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3))
    | ~ spl4_3
    | ~ spl4_35 ),
    inference(superposition,[],[f593,f41])).

fof(f41,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_3
  <=> k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f593,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl4_35
  <=> ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f46,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_4
  <=> k1_tarski(sK3) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f594,plain,
    ( spl4_35
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f111,f81,f77,f592])).

fof(f77,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f81,plain,
    ( spl4_11
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f111,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(superposition,[],[f78,f83])).

fof(f83,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f78,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f564,plain,
    ( spl4_30
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f135,f131,f53,f561])).

fof(f53,plain,
    ( spl4_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f131,plain,
    ( spl4_17
  <=> k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f135,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(superposition,[],[f133,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f133,plain,
    ( k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( spl4_17
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f110,f99,f49,f34,f131])).

fof(f34,plain,
    ( spl4_2
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_5
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f99,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f110,plain,
    ( k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f102,f50])).

fof(f50,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f102,plain,
    ( k2_tarski(sK3,sK3) = k3_xboole_0(k2_tarski(sK3,sK3),sK0)
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f36,f36,f100])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f36,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f101,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f27,f99])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f84,plain,
    ( spl4_11
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f64,f61,f29,f81])).

fof(f29,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f61,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f64,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f31,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f31,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f79,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f26,f77])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f63,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f42,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.42  % (29682)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (29682)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f638,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f51,f55,f63,f79,f84,f101,f134,f564,f594,f621])).
% 0.21/0.45  fof(f621,plain,(
% 0.21/0.45    ~spl4_3 | spl4_4 | ~spl4_30 | ~spl4_35),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f620])).
% 0.21/0.45  fof(f620,plain,(
% 0.21/0.45    $false | (~spl4_3 | spl4_4 | ~spl4_30 | ~spl4_35)),
% 0.21/0.45    inference(subsumption_resolution,[],[f46,f619])).
% 0.21/0.45  fof(f619,plain,(
% 0.21/0.45    k1_tarski(sK3) = k3_xboole_0(sK0,sK2) | (~spl4_3 | ~spl4_30 | ~spl4_35)),
% 0.21/0.45    inference(forward_demodulation,[],[f595,f563])).
% 0.21/0.45  fof(f563,plain,(
% 0.21/0.45    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) | ~spl4_30),
% 0.21/0.45    inference(avatar_component_clause,[],[f561])).
% 0.21/0.45  fof(f561,plain,(
% 0.21/0.45    spl4_30 <=> k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.45  fof(f595,plain,(
% 0.21/0.45    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3)) | (~spl4_3 | ~spl4_35)),
% 0.21/0.45    inference(superposition,[],[f593,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) | ~spl4_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl4_3 <=> k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f593,plain,(
% 0.21/0.45    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | ~spl4_35),
% 0.21/0.45    inference(avatar_component_clause,[],[f592])).
% 0.21/0.45  fof(f592,plain,(
% 0.21/0.45    spl4_35 <=> ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) | spl4_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl4_4 <=> k1_tarski(sK3) = k3_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.45  fof(f594,plain,(
% 0.21/0.45    spl4_35 | ~spl4_10 | ~spl4_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f111,f81,f77,f592])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    spl4_10 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl4_11 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) ) | (~spl4_10 | ~spl4_11)),
% 0.21/0.45    inference(superposition,[],[f78,f83])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl4_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f77])).
% 0.21/0.45  fof(f564,plain,(
% 0.21/0.45    spl4_30 | ~spl4_6 | ~spl4_17),
% 0.21/0.45    inference(avatar_split_clause,[],[f135,f131,f53,f561])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl4_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    spl4_17 <=> k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    k1_tarski(sK3) = k3_xboole_0(sK0,k1_tarski(sK3)) | (~spl4_6 | ~spl4_17)),
% 0.21/0.45    inference(superposition,[],[f133,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl4_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f53])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) | ~spl4_17),
% 0.21/0.45    inference(avatar_component_clause,[],[f131])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    spl4_17 | ~spl4_2 | ~spl4_5 | ~spl4_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f110,f99,f49,f34,f131])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    spl4_2 <=> r2_hidden(sK3,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl4_5 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    spl4_12 <=> ! [X1,X0,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK0) | (~spl4_2 | ~spl4_5 | ~spl4_12)),
% 0.21/0.45    inference(forward_demodulation,[],[f102,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl4_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f49])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    k2_tarski(sK3,sK3) = k3_xboole_0(k2_tarski(sK3,sK3),sK0) | (~spl4_2 | ~spl4_12)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f36,f36,f100])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) ) | ~spl4_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f99])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    r2_hidden(sK3,sK0) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl4_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f99])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl4_11 | ~spl4_1 | ~spl4_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f64,f61,f29,f81])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl4_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    sK0 = k3_xboole_0(sK0,sK1) | (~spl4_1 | ~spl4_8)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f31,f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f61])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1) | ~spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f29])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl4_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f77])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl4_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f61])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f44])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f39])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f34])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    r2_hidden(sK3,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f29])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (29682)------------------------------
% 0.21/0.46  % (29682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (29682)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (29682)Memory used [KB]: 6908
% 0.21/0.46  % (29682)Time elapsed: 0.034 s
% 0.21/0.46  % (29682)------------------------------
% 0.21/0.46  % (29682)------------------------------
% 0.21/0.46  % (29676)Success in time 0.099 s
%------------------------------------------------------------------------------
