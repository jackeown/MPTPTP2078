%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:11 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 124 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  142 ( 284 expanded)
%              Number of equality atoms :   38 ( 103 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f54,f59,f66,f70])).

fof(f70,plain,
    ( ~ spl2_2
    | spl2_5
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl2_2
    | spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f67,f53])).

fof(f53,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_5
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f67,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f65,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_7
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f66,plain,
    ( spl2_7
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f61,f56,f43,f63])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f56,plain,
    ( spl2_6
  <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f61,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f44,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f59,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f49,f39,f31,f56])).

fof(f31,plain,
    ( spl2_1
  <=> ! [X1,X0] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f49,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f25,f48])).

fof(f48,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f24,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f15,f17,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f15,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f25,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f14,f17,f23])).

fof(f14,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f48,f39,f31,f51])).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f43])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f39])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f17])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f35])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f26,f31])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (23633)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.13/0.41  % (23633)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f71,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f54,f59,f66,f70])).
% 0.13/0.41  fof(f70,plain,(
% 0.13/0.41    ~spl2_2 | spl2_5 | ~spl2_7),
% 0.13/0.41    inference(avatar_contradiction_clause,[],[f69])).
% 0.13/0.41  fof(f69,plain,(
% 0.13/0.41    $false | (~spl2_2 | spl2_5 | ~spl2_7)),
% 0.13/0.41    inference(subsumption_resolution,[],[f67,f53])).
% 0.13/0.41  fof(f53,plain,(
% 0.13/0.41    ~r2_hidden(sK0,sK1) | spl2_5),
% 0.13/0.41    inference(avatar_component_clause,[],[f51])).
% 0.13/0.41  fof(f51,plain,(
% 0.13/0.41    spl2_5 <=> r2_hidden(sK0,sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.13/0.41  fof(f67,plain,(
% 0.13/0.41    r2_hidden(sK0,sK1) | (~spl2_2 | ~spl2_7)),
% 0.13/0.41    inference(resolution,[],[f65,f36])).
% 0.13/0.41  fof(f36,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_2),
% 0.13/0.41    inference(avatar_component_clause,[],[f35])).
% 0.13/0.41  fof(f35,plain,(
% 0.13/0.41    spl2_2 <=> ! [X1,X0] : (r2_hidden(X0,X1) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.13/0.41  fof(f65,plain,(
% 0.13/0.41    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_7),
% 0.13/0.41    inference(avatar_component_clause,[],[f63])).
% 0.13/0.41  fof(f63,plain,(
% 0.13/0.41    spl2_7 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.13/0.41  fof(f66,plain,(
% 0.13/0.41    spl2_7 | ~spl2_4 | ~spl2_6),
% 0.13/0.41    inference(avatar_split_clause,[],[f61,f56,f43,f63])).
% 0.13/0.41  fof(f43,plain,(
% 0.13/0.41    spl2_4 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.13/0.41  fof(f56,plain,(
% 0.13/0.41    spl2_6 <=> k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.13/0.41  fof(f61,plain,(
% 0.13/0.41    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl2_4 | ~spl2_6)),
% 0.13/0.41    inference(trivial_inequality_removal,[],[f60])).
% 0.13/0.41  fof(f60,plain,(
% 0.13/0.41    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl2_4 | ~spl2_6)),
% 0.13/0.41    inference(superposition,[],[f44,f58])).
% 0.13/0.41  fof(f58,plain,(
% 0.13/0.41    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~spl2_6),
% 0.13/0.41    inference(avatar_component_clause,[],[f56])).
% 0.13/0.41  fof(f44,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) ) | ~spl2_4),
% 0.13/0.41    inference(avatar_component_clause,[],[f43])).
% 0.13/0.41  fof(f59,plain,(
% 0.13/0.41    spl2_6 | ~spl2_1 | ~spl2_3),
% 0.13/0.41    inference(avatar_split_clause,[],[f49,f39,f31,f56])).
% 0.13/0.41  fof(f31,plain,(
% 0.13/0.41    spl2_1 <=> ! [X1,X0] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.13/0.41  fof(f39,plain,(
% 0.13/0.41    spl2_3 <=> ! [X1,X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 0.13/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.13/0.41  fof(f49,plain,(
% 0.13/0.41    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | (~spl2_1 | ~spl2_3)),
% 0.13/0.41    inference(subsumption_resolution,[],[f25,f48])).
% 0.13/0.41  fof(f48,plain,(
% 0.13/0.41    ~r2_hidden(sK0,sK1) | (~spl2_1 | ~spl2_3)),
% 0.13/0.41    inference(subsumption_resolution,[],[f24,f47])).
% 0.13/0.41  fof(f47,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) | ~r2_hidden(X0,X1)) ) | (~spl2_1 | ~spl2_3)),
% 0.13/0.41    inference(resolution,[],[f40,f32])).
% 0.13/0.41  fof(f32,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_1),
% 0.13/0.41    inference(avatar_component_clause,[],[f31])).
% 0.13/0.41  fof(f40,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_3),
% 0.13/0.41    inference(avatar_component_clause,[],[f39])).
% 0.13/0.41  fof(f24,plain,(
% 0.13/0.41    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.13/0.41    inference(definition_unfolding,[],[f15,f17,f23])).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f16,f18])).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.13/0.41  fof(f10,plain,(
% 0.13/0.41    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f9,plain,(
% 0.13/0.41    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 0.13/0.41    inference(nnf_transformation,[],[f8])).
% 0.13/0.41  fof(f8,plain,(
% 0.13/0.41    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f7])).
% 0.13/0.41  fof(f7,negated_conjecture,(
% 0.13/0.41    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.13/0.41    inference(negated_conjecture,[],[f6])).
% 0.13/0.41  fof(f6,conjecture,(
% 0.13/0.41    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.13/0.41    inference(definition_unfolding,[],[f14,f17,f23])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f11])).
% 0.13/0.41  fof(f54,plain,(
% 0.13/0.41    ~spl2_5 | ~spl2_1 | ~spl2_3),
% 0.13/0.41    inference(avatar_split_clause,[],[f48,f39,f31,f51])).
% 0.13/0.41  fof(f45,plain,(
% 0.13/0.41    spl2_4),
% 0.13/0.41    inference(avatar_split_clause,[],[f29,f43])).
% 0.13/0.41  fof(f29,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.13/0.41    inference(definition_unfolding,[],[f21,f17])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.13/0.41    inference(nnf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.13/0.41  fof(f41,plain,(
% 0.13/0.41    spl2_3),
% 0.13/0.41    inference(avatar_split_clause,[],[f28,f39])).
% 0.13/0.41  fof(f28,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f22,f17])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f13])).
% 0.13/0.41  fof(f37,plain,(
% 0.13/0.41    spl2_2),
% 0.13/0.41    inference(avatar_split_clause,[],[f27,f35])).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f19,f23])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f12])).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.13/0.41    inference(nnf_transformation,[],[f5])).
% 0.13/0.41  fof(f5,axiom,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.13/0.41  fof(f33,plain,(
% 0.13/0.41    spl2_1),
% 0.13/0.41    inference(avatar_split_clause,[],[f26,f31])).
% 0.13/0.41  fof(f26,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.13/0.41    inference(definition_unfolding,[],[f20,f23])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f12])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (23633)------------------------------
% 0.13/0.41  % (23633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (23633)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (23633)Memory used [KB]: 6140
% 0.13/0.41  % (23633)Time elapsed: 0.005 s
% 0.13/0.41  % (23633)------------------------------
% 0.13/0.41  % (23633)------------------------------
% 0.13/0.42  % (23625)Success in time 0.059 s
%------------------------------------------------------------------------------
