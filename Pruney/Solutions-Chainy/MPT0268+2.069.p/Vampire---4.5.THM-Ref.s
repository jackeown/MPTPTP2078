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
% DateTime   : Thu Dec  3 12:40:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 116 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  126 ( 212 expanded)
%              Number of equality atoms :   39 (  85 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f76,f101,f110,f121,f143])).

fof(f143,plain,
    ( spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f133,f75])).

fof(f75,plain,
    ( ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_3
  <=> r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f133,plain,
    ( r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f44,f100])).

fof(f100,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_5
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f121,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f109,f114])).

fof(f114,plain,
    ( r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f44,f50])).

fof(f50,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f109,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f55,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f110,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f105,f53,f49])).

fof(f105,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f37,f55])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f21,f25,f35])).

fof(f21,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f101,plain,
    ( spl2_5
    | spl2_2 ),
    inference(avatar_split_clause,[],[f77,f53,f98])).

fof(f77,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f54,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) ),
    inference(definition_unfolding,[],[f33,f35,f25,f35])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f76,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f63,f49,f73])).

fof(f63,plain,
    ( ~ r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f51,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f56,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f36,f53,f49])).

fof(f36,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f22,f25,f35])).

fof(f22,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (9900)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.44  % (9900)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f146,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f56,f76,f101,f110,f121,f143])).
% 0.20/0.44  fof(f143,plain,(
% 0.20/0.44    spl2_3 | ~spl2_5),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.44  fof(f142,plain,(
% 0.20/0.44    $false | (spl2_3 | ~spl2_5)),
% 0.20/0.44    inference(subsumption_resolution,[],[f133,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f73])).
% 0.20/0.44  fof(f73,plain,(
% 0.20/0.44    spl2_3 <=> r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_5),
% 0.20/0.44    inference(superposition,[],[f44,f100])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    k2_enumset1(sK1,sK1,sK1,sK1) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | ~spl2_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f98])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    spl2_5 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f38,f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f24,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.44  fof(f121,plain,(
% 0.20/0.44    ~spl2_1 | ~spl2_2),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f120])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    $false | (~spl2_1 | ~spl2_2)),
% 0.20/0.44    inference(subsumption_resolution,[],[f109,f114])).
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_1),
% 0.20/0.44    inference(superposition,[],[f44,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl2_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    spl2_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_2),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f55,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f34,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.44    inference(definition_unfolding,[],[f23,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    r2_hidden(sK1,sK0) | ~spl2_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f53])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    spl2_2 <=> r2_hidden(sK1,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    spl2_1 | ~spl2_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f105,f53,f49])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl2_2),
% 0.20/0.44    inference(subsumption_resolution,[],[f37,f55])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.44    inference(definition_unfolding,[],[f21,f25,f35])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 0.20/0.44    inference(nnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    spl2_5 | spl2_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f77,f53,f98])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    k2_enumset1(sK1,sK1,sK1,sK1) = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)) | spl2_2),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f54,f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f33,f35,f25,f35])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    ~r2_hidden(sK1,sK0) | spl2_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f53])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    ~spl2_3 | spl2_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f63,f49,f73])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ~r1_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_1),
% 0.20/0.44    inference(unit_resulting_resolution,[],[f51,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.44    inference(definition_unfolding,[],[f30,f25])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | spl2_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f49])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ~spl2_1 | spl2_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f36,f53,f49])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.44    inference(definition_unfolding,[],[f22,f25,f35])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (9900)------------------------------
% 0.20/0.44  % (9900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (9900)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (9900)Memory used [KB]: 10618
% 0.20/0.44  % (9900)Time elapsed: 0.038 s
% 0.20/0.44  % (9900)------------------------------
% 0.20/0.44  % (9900)------------------------------
% 0.20/0.44  % (9884)Success in time 0.091 s
%------------------------------------------------------------------------------
