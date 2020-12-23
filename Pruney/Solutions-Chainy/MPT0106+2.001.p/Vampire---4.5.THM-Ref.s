%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  57 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f24,f49,f63])).

fof(f63,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f13,f58])).

fof(f58,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X0,X1)),X2) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X2)),k4_xboole_0(X0,k2_xboole_0(X1,X2)))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f48,f16])).

fof(f16,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl3_1
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_4
  <=> ! [X1,X3,X0,X2] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f13,plain,(
    k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(definition_unfolding,[],[f9,f10])).

fof(f10,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f9,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
   => k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f49,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f25,f22,f15,f47])).

fof(f22,plain,
    ( spl3_2
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f25,plain,
    ( ! [X2,X0,X3,X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f23,f16])).

fof(f23,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f24,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f17,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f11,f15])).

fof(f11,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (4649)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.43  % (4649)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f17,f24,f49,f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ~spl3_1 | ~spl3_4),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    $false | (~spl3_1 | ~spl3_4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f13,f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X0,X1)),X2) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(X4,X2)),k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ) | (~spl3_1 | ~spl3_4)),
% 0.20/0.43    inference(superposition,[],[f48,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    spl3_1 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2))) ) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl3_4 <=> ! [X1,X3,X0,X2] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)),
% 0.20/0.43    inference(definition_unfolding,[],[f9,f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)))),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) => k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 0.20/0.43    inference(negated_conjecture,[],[f4])).
% 0.20/0.43  fof(f4,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl3_4 | ~spl3_1 | ~spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f22,f15,f47])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    spl3_2 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X3),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X3,X2))) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.43    inference(superposition,[],[f23,f16])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f22])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f12,f22])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f11,f15])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (4649)------------------------------
% 0.20/0.43  % (4649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (4649)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (4649)Memory used [KB]: 6140
% 0.20/0.43  % (4649)Time elapsed: 0.028 s
% 0.20/0.43  % (4649)------------------------------
% 0.20/0.43  % (4649)------------------------------
% 0.20/0.44  % (4641)Success in time 0.085 s
%------------------------------------------------------------------------------
