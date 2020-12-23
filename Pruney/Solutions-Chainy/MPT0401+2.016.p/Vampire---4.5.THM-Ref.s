%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  95 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  156 ( 247 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f56,f63,f71,f87,f96,f101])).

fof(f101,plain,
    ( spl3_2
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl3_2
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f37,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f97,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_7
  <=> r1_tarski(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_tarski(sK1),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_14
  <=> ! [X0] :
        ( r1_tarski(sK2,X0)
        | ~ r1_tarski(k3_tarski(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f96,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f92,f85,f30,f94])).

fof(f30,plain,
    ( spl3_1
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f85,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k3_tarski(X0),X1)
        | r1_tarski(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f92,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,X0)
        | ~ r1_tarski(k3_tarski(sK1),X0) )
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f86,f32])).

fof(f32,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X0)
        | r1_tarski(X2,X1)
        | ~ r1_tarski(k3_tarski(X0),X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,
    ( spl3_12
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f72,f69,f49,f85])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),X1)
        | r1_tarski(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f63,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f58,f54,f45,f40,f60])).

fof(f40,plain,
    ( spl3_3
  <=> r1_setfam_1(sK1,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( spl3_4
  <=> ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f58,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f57,f46])).

fof(f46,plain,
    ( ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f57,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(sK0,sK0)))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,
    ( r1_setfam_1(sK1,k2_tarski(sK0,sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        | r1_tarski(k3_tarski(X0),k3_tarski(X1)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f45])).

fof(f28,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f40])).

fof(f27,plain,(
    r1_setfam_1(sK1,k2_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f38,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f30])).

fof(f19,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (12304)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (12304)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f56,f63,f71,f87,f96,f101])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    spl3_2 | ~spl3_7 | ~spl3_14),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    $false | (spl3_2 | ~spl3_7 | ~spl3_14)),
% 0.21/0.45    inference(subsumption_resolution,[],[f97,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ~r1_tarski(sK2,sK0) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl3_2 <=> r1_tarski(sK2,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    r1_tarski(sK2,sK0) | (~spl3_7 | ~spl3_14)),
% 0.21/0.45    inference(resolution,[],[f95,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    r1_tarski(k3_tarski(sK1),sK0) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl3_7 <=> r1_tarski(k3_tarski(sK1),sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(k3_tarski(sK1),X0) | r1_tarski(sK2,X0)) ) | ~spl3_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    spl3_14 <=> ! [X0] : (r1_tarski(sK2,X0) | ~r1_tarski(k3_tarski(sK1),X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    spl3_14 | ~spl3_1 | ~spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f92,f85,f30,f94])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl3_1 <=> r2_hidden(sK2,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl3_12 <=> ! [X1,X0,X2] : (~r1_tarski(k3_tarski(X0),X1) | r1_tarski(X2,X1) | ~r2_hidden(X2,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(sK2,X0) | ~r1_tarski(k3_tarski(sK1),X0)) ) | (~spl3_1 | ~spl3_12)),
% 0.21/0.45    inference(resolution,[],[f86,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    r2_hidden(sK2,sK1) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f30])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r1_tarski(X2,X1) | ~r1_tarski(k3_tarski(X0),X1)) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f85])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    spl3_12 | ~spl3_5 | ~spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f72,f69,f49,f85])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl3_5 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl3_9 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | r1_tarski(X2,X1) | ~r2_hidden(X2,X0)) ) | (~spl3_5 | ~spl3_9)),
% 0.21/0.45    inference(resolution,[],[f70,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) ) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f49])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f69])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f69])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl3_7 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f58,f54,f45,f40,f60])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl3_3 <=> r1_setfam_1(sK1,k2_tarski(sK0,sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl3_4 <=> ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    spl3_6 <=> ! [X1,X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    r1_tarski(k3_tarski(sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.21/0.45    inference(forward_demodulation,[],[f57,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) ) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f45])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(sK0,sK0))) | (~spl3_3 | ~spl3_6)),
% 0.21/0.45    inference(resolution,[],[f55,f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    r1_setfam_1(sK1,k2_tarski(sK0,sK0)) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f40])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f54])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f54])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f49])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f45])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.45    inference(rectify,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f40])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    r1_setfam_1(sK1,k2_tarski(sK0,sK0))),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f20,f35])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ~r1_tarski(sK2,sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f30])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    r2_hidden(sK2,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (12304)------------------------------
% 0.21/0.45  % (12304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (12304)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (12304)Memory used [KB]: 6140
% 0.21/0.45  % (12304)Time elapsed: 0.009 s
% 0.21/0.45  % (12304)------------------------------
% 0.21/0.45  % (12304)------------------------------
% 0.21/0.45  % (12309)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (12297)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (12293)Success in time 0.097 s
%------------------------------------------------------------------------------
