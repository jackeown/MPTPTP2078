%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  51 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 125 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f40,f42])).

fof(f42,plain,
    ( ~ spl3_3
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f41,f37,f26,f31])).

fof(f31,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f26,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( spl3_4
  <=> r1_tarski(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK0,sK1)
    | spl3_4 ),
    inference(resolution,[],[f18,f39])).

fof(f39,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f40,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f35,f21,f37])).

fof(f21,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(resolution,[],[f17,f23])).

fof(f23,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f21])).

fof(f19,plain,(
    ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f15,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:42:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.41  % (5830)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (5830)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f24,f29,f34,f40,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ~spl3_3 | ~spl3_2 | spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f41,f37,f26,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl3_4 <=> r1_tarski(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ~r1_tarski(sK2,sK1) | ~r1_tarski(sK0,sK1) | spl3_4),
% 0.22/0.48    inference(resolution,[],[f18,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ~r1_tarski(k2_xboole_0(sK0,sK2),sK1) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f37])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ~spl3_4 | spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f21,f37])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    spl3_1 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~r1_tarski(k2_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.22/0.48    inference(resolution,[],[f17,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f21])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f13,f31])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f14,f26])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    r1_tarski(sK2,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f21])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),sK1)),
% 0.22/0.48    inference(definition_unfolding,[],[f15,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (5830)------------------------------
% 0.22/0.48  % (5830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5830)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (5830)Memory used [KB]: 6012
% 0.22/0.48  % (5830)Time elapsed: 0.069 s
% 0.22/0.48  % (5830)------------------------------
% 0.22/0.48  % (5830)------------------------------
% 0.22/0.49  % (5815)Success in time 0.126 s
%------------------------------------------------------------------------------
