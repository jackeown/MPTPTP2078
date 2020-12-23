%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 (  90 expanded)
%              Number of leaves         :   21 (  41 expanded)
%              Depth                    :    6
%              Number of atoms          :  141 ( 190 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f38,f46,f50,f59,f64,f70,f87,f95,f97,f110,f112])).

fof(f112,plain,
    ( ~ spl2_5
    | spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl2_5
    | spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f90,f109])).

fof(f109,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_14
  <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f90,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl2_5
    | spl2_12 ),
    inference(unit_resulting_resolution,[],[f86,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f86,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_12
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f110,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f66,f62,f36,f108])).

fof(f36,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f66,plain,
    ( ! [X2,X0] : r1_tarski(k3_xboole_0(X2,X0),X0)
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(superposition,[],[f63,f37])).

fof(f37,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f63,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f97,plain,
    ( ~ spl2_5
    | spl2_11
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl2_5
    | spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f88,f94])).

fof(f94,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_13
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f88,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ spl2_5
    | spl2_11 ),
    inference(unit_resulting_resolution,[],[f82,f45])).

fof(f82,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_11
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f95,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f55,f48,f32,f93])).

fof(f32,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f48,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f55,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(superposition,[],[f33,f49])).

fof(f49,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f33,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f87,plain,
    ( ~ spl2_11
    | ~ spl2_12
    | spl2_1
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f73,f68,f27,f84,f80])).

fof(f27,plain,
    ( spl2_1
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f68,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f73,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))
    | spl2_1
    | ~ spl2_9 ),
    inference(resolution,[],[f69,f29])).

fof(f29,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f64,plain,
    ( spl2_8
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f60,f57,f62])).

fof(f57,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f60,plain,
    ( ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f58,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f58,plain,
    ( ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f50,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f38,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f30,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (31773)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.45  % (31778)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.46  % (31778)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f113,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f30,f34,f38,f46,f50,f59,f64,f70,f87,f95,f97,f110,f112])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    ~spl2_5 | spl2_12 | ~spl2_14),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f111])).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    $false | (~spl2_5 | spl2_12 | ~spl2_14)),
% 0.19/0.46    inference(subsumption_resolution,[],[f90,f109])).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | ~spl2_14),
% 0.19/0.46    inference(avatar_component_clause,[],[f108])).
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    spl2_14 <=> ! [X0,X2] : r1_tarski(k3_xboole_0(X2,X0),X0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.19/0.46  fof(f90,plain,(
% 0.19/0.46    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | (~spl2_5 | spl2_12)),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f86,f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_5),
% 0.19/0.46    inference(avatar_component_clause,[],[f44])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    spl2_5 <=> ! [X1,X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) | spl2_12),
% 0.19/0.46    inference(avatar_component_clause,[],[f84])).
% 0.19/0.46  fof(f84,plain,(
% 0.19/0.46    spl2_12 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    spl2_14 | ~spl2_3 | ~spl2_8),
% 0.19/0.46    inference(avatar_split_clause,[],[f66,f62,f36,f108])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    spl2_3 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    spl2_8 <=> ! [X1,X0,X2] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.46  fof(f66,plain,(
% 0.19/0.46    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X2,X0),X0)) ) | (~spl2_3 | ~spl2_8)),
% 0.19/0.46    inference(superposition,[],[f63,f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f36])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_8),
% 0.19/0.46    inference(avatar_component_clause,[],[f62])).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    ~spl2_5 | spl2_11 | ~spl2_13),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f96])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    $false | (~spl2_5 | spl2_11 | ~spl2_13)),
% 0.19/0.46    inference(subsumption_resolution,[],[f88,f94])).
% 0.19/0.46  fof(f94,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_13),
% 0.19/0.46    inference(avatar_component_clause,[],[f93])).
% 0.19/0.46  fof(f93,plain,(
% 0.19/0.46    spl2_13 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | (~spl2_5 | spl2_11)),
% 0.19/0.46    inference(unit_resulting_resolution,[],[f82,f45])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) | spl2_11),
% 0.19/0.46    inference(avatar_component_clause,[],[f80])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    spl2_11 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    spl2_13 | ~spl2_2 | ~spl2_6),
% 0.19/0.46    inference(avatar_split_clause,[],[f55,f48,f32,f93])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    spl2_2 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | (~spl2_2 | ~spl2_6)),
% 0.19/0.46    inference(superposition,[],[f33,f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_6),
% 0.19/0.46    inference(avatar_component_clause,[],[f48])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f32])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    ~spl2_11 | ~spl2_12 | spl2_1 | ~spl2_9),
% 0.19/0.46    inference(avatar_split_clause,[],[f73,f68,f27,f84,f80])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    spl2_1 <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    spl2_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) | ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) | (spl2_1 | ~spl2_9)),
% 0.19/0.46    inference(resolution,[],[f69,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | spl2_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f27])).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_9),
% 0.19/0.46    inference(avatar_component_clause,[],[f68])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    spl2_9),
% 0.19/0.46    inference(avatar_split_clause,[],[f25,f68])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.19/0.46  fof(f64,plain,(
% 0.19/0.46    spl2_8 | ~spl2_7),
% 0.19/0.46    inference(avatar_split_clause,[],[f60,f57,f62])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    spl2_7 <=> ! [X1,X0,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_7),
% 0.19/0.46    inference(forward_demodulation,[],[f58,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) ) | ~spl2_7),
% 0.19/0.46    inference(avatar_component_clause,[],[f57])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    spl2_7),
% 0.19/0.46    inference(avatar_split_clause,[],[f23,f57])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    spl2_6),
% 0.19/0.46    inference(avatar_split_clause,[],[f21,f48])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.46    inference(cnf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    spl2_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f22,f44])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    spl2_3),
% 0.19/0.46    inference(avatar_split_clause,[],[f19,f36])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    spl2_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f18,f32])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ~spl2_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f17,f27])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) => ~r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ? [X0,X1] : ~r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.46    inference(negated_conjecture,[],[f9])).
% 0.19/0.46  fof(f9,conjecture,(
% 0.19/0.46    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (31778)------------------------------
% 0.19/0.46  % (31778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (31778)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (31778)Memory used [KB]: 6140
% 0.19/0.46  % (31778)Time elapsed: 0.058 s
% 0.19/0.46  % (31778)------------------------------
% 0.19/0.46  % (31778)------------------------------
% 0.19/0.46  % (31777)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (31779)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (31772)Success in time 0.107 s
%------------------------------------------------------------------------------
