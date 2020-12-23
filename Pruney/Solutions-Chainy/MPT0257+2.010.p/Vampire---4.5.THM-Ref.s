%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  37 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  74 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f24,f28,f31])).

fof(f31,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f30])).

fof(f30,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f29,f23])).

fof(f23,plain,
    ( k1_tarski(sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f29,plain,
    ( k1_tarski(sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f27,f18])).

fof(f18,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0)))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f28,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f12,f11])).

fof(f11,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f24,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    k1_tarski(sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f10,f11])).

fof(f10,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f19,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f9,f16])).

fof(f9,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:50:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (20760)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (20760)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f19,f24,f28,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ~spl2_1 | spl2_2 | ~spl2_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    $false | (~spl2_1 | spl2_2 | ~spl2_3)),
% 0.21/0.43    inference(subsumption_resolution,[],[f29,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    k1_tarski(sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    spl2_2 <=> k1_tarski(sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    k1_tarski(sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))) | (~spl2_1 | ~spl2_3)),
% 0.21/0.43    inference(resolution,[],[f27,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0)))) ) | ~spl2_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    spl2_3 <=> ! [X1,X0] : (k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) | ~r2_hidden(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl2_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f12,f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f21])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    k1_tarski(sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.43    inference(definition_unfolding,[],[f10,f11])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f3])).
% 0.21/0.43  fof(f3,conjecture,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f9,f16])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (20760)------------------------------
% 0.21/0.43  % (20760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (20760)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (20760)Memory used [KB]: 6012
% 0.21/0.43  % (20760)Time elapsed: 0.003 s
% 0.21/0.43  % (20760)------------------------------
% 0.21/0.43  % (20760)------------------------------
% 0.21/0.44  % (20752)Success in time 0.069 s
%------------------------------------------------------------------------------
