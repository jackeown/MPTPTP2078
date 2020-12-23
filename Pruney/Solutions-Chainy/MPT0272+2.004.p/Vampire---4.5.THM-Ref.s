%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:12 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   29 (  38 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   75 (  97 expanded)
%              Number of equality atoms :   50 (  68 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f83,f149,f169])).

fof(f169,plain,
    ( spl2_1
    | spl2_2
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl2_1
    | spl2_2
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f43,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f48,f82,f148])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,X2) != k1_tarski(X0)
        | k1_tarski(X0) = X2
        | k1_xboole_0 = X2 )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl2_14
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X2
        | k1_tarski(X0) = X2
        | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f82,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f48,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f43,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f149,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f39,f147])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f83,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f49,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f44,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:08:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.42  % (12274)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.43  % (12274)Refutation found. Thanks to Tanya!
% 0.23/0.43  % SZS status Theorem for theBenchmark
% 0.23/0.43  % SZS output start Proof for theBenchmark
% 0.23/0.43  fof(f173,plain,(
% 0.23/0.43    $false),
% 0.23/0.43    inference(avatar_sat_refutation,[],[f44,f49,f83,f149,f169])).
% 0.23/0.43  fof(f169,plain,(
% 0.23/0.43    spl2_1 | spl2_2 | ~spl2_10 | ~spl2_14),
% 0.23/0.43    inference(avatar_contradiction_clause,[],[f168])).
% 0.23/0.43  fof(f168,plain,(
% 0.23/0.43    $false | (spl2_1 | spl2_2 | ~spl2_10 | ~spl2_14)),
% 0.23/0.43    inference(subsumption_resolution,[],[f43,f161])).
% 0.23/0.43  fof(f161,plain,(
% 0.23/0.43    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | (spl2_2 | ~spl2_10 | ~spl2_14)),
% 0.23/0.43    inference(unit_resulting_resolution,[],[f48,f82,f148])).
% 0.23/0.43  fof(f148,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) != k1_tarski(X0) | k1_tarski(X0) = X2 | k1_xboole_0 = X2) ) | ~spl2_14),
% 0.23/0.43    inference(avatar_component_clause,[],[f147])).
% 0.23/0.43  fof(f147,plain,(
% 0.23/0.43    spl2_14 <=> ! [X1,X0,X2] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.23/0.43  fof(f82,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_10),
% 0.23/0.43    inference(avatar_component_clause,[],[f81])).
% 0.23/0.43  fof(f81,plain,(
% 0.23/0.43    spl2_10 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.43  fof(f48,plain,(
% 0.23/0.43    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.23/0.43    inference(avatar_component_clause,[],[f46])).
% 0.23/0.43  fof(f46,plain,(
% 0.23/0.43    spl2_2 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.43  fof(f43,plain,(
% 0.23/0.43    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_1),
% 0.23/0.43    inference(avatar_component_clause,[],[f41])).
% 0.23/0.43  fof(f41,plain,(
% 0.23/0.43    spl2_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.43  fof(f149,plain,(
% 0.23/0.43    spl2_14),
% 0.23/0.43    inference(avatar_split_clause,[],[f39,f147])).
% 0.23/0.43  fof(f39,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 0.23/0.43    inference(duplicate_literal_removal,[],[f35])).
% 0.23/0.43  fof(f35,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f14])).
% 0.23/0.43  fof(f14,plain,(
% 0.23/0.43    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 0.23/0.43    inference(ennf_transformation,[],[f10])).
% 0.23/0.43  fof(f10,axiom,(
% 0.23/0.43    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.23/0.43  fof(f83,plain,(
% 0.23/0.43    spl2_10),
% 0.23/0.43    inference(avatar_split_clause,[],[f26,f81])).
% 0.23/0.43  fof(f26,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.43    inference(cnf_transformation,[],[f8])).
% 0.23/0.43  fof(f8,axiom,(
% 0.23/0.43    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.23/0.43  fof(f49,plain,(
% 0.23/0.43    ~spl2_2),
% 0.23/0.43    inference(avatar_split_clause,[],[f18,f46])).
% 0.23/0.43  fof(f18,plain,(
% 0.23/0.43    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.43    inference(cnf_transformation,[],[f16])).
% 0.23/0.43  fof(f16,plain,(
% 0.23/0.43    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 0.23/0.43  fof(f15,plain,(
% 0.23/0.43    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.23/0.43    introduced(choice_axiom,[])).
% 0.23/0.43  fof(f13,plain,(
% 0.23/0.43    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.43    inference(ennf_transformation,[],[f12])).
% 0.23/0.43  fof(f12,negated_conjecture,(
% 0.23/0.43    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.43    inference(negated_conjecture,[],[f11])).
% 0.23/0.43  fof(f11,conjecture,(
% 0.23/0.43    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.23/0.43  fof(f44,plain,(
% 0.23/0.43    ~spl2_1),
% 0.23/0.43    inference(avatar_split_clause,[],[f17,f41])).
% 0.23/0.43  fof(f17,plain,(
% 0.23/0.43    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.23/0.43    inference(cnf_transformation,[],[f16])).
% 0.23/0.43  % SZS output end Proof for theBenchmark
% 0.23/0.43  % (12274)------------------------------
% 0.23/0.43  % (12274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.43  % (12274)Termination reason: Refutation
% 0.23/0.43  
% 0.23/0.43  % (12274)Memory used [KB]: 6140
% 0.23/0.43  % (12274)Time elapsed: 0.008 s
% 0.23/0.43  % (12274)------------------------------
% 0.23/0.43  % (12274)------------------------------
% 0.23/0.43  % (12266)Success in time 0.065 s
%------------------------------------------------------------------------------
