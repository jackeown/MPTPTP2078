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
% DateTime   : Thu Dec  3 12:30:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  47 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 116 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f34,f36])).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f35])).

fof(f35,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f27,f13])).

fof(f13,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( r1_xboole_0(sK1,sK0)
    & r1_tarski(sK1,sK0)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(X1,X0)
        & r1_tarski(X1,X0)
        & ~ v1_xboole_0(X1) )
   => ( r1_xboole_0(sK1,sK0)
      & r1_tarski(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ~ ( r1_xboole_0(X1,X0)
            & r1_tarski(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f27,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f31,f14])).

fof(f14,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f32,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f23,f29,f25])).

fof(f23,plain,
    ( ~ r1_tarski(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f16,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f22,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X0,sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:47:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.43  % (5378)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.43  % (5382)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.43  % (5382)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f32,f34,f36])).
% 0.19/0.43  fof(f36,plain,(
% 0.19/0.43    ~spl2_1),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f35])).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    $false | ~spl2_1),
% 0.19/0.43    inference(resolution,[],[f27,f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ~v1_xboole_0(sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1)) => (r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f8,plain,(
% 0.19/0.43    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1))),
% 0.19/0.43    inference(flattening,[],[f7])).
% 0.19/0.43  fof(f7,plain,(
% 0.19/0.43    ? [X0,X1] : ((r1_xboole_0(X1,X0) & r1_tarski(X1,X0)) & ~v1_xboole_0(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.19/0.43    inference(negated_conjecture,[],[f5])).
% 0.19/0.43  fof(f5,conjecture,(
% 0.19/0.43    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    v1_xboole_0(sK1) | ~spl2_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f25])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    spl2_1 <=> v1_xboole_0(sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.43  fof(f34,plain,(
% 0.19/0.43    spl2_2),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f33])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    $false | spl2_2),
% 0.19/0.43    inference(resolution,[],[f31,f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    r1_tarski(sK1,sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f12])).
% 0.19/0.43  fof(f31,plain,(
% 0.19/0.43    ~r1_tarski(sK1,sK0) | spl2_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f29])).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    spl2_2 <=> r1_tarski(sK1,sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    spl2_1 | ~spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f23,f29,f25])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ~r1_tarski(sK1,sK0) | v1_xboole_0(sK1)),
% 0.19/0.43    inference(resolution,[],[f22,f21])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.19/0.43    inference(superposition,[],[f16,f20])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.19/0.43    inference(definition_unfolding,[],[f17,f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.19/0.43    inference(cnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(X0,sK0) | v1_xboole_0(X0)) )),
% 0.19/0.43    inference(resolution,[],[f19,f15])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    r1_xboole_0(sK1,sK0)),
% 0.19/0.43    inference(cnf_transformation,[],[f12])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.19/0.43    inference(flattening,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.19/0.43    inference(ennf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (5382)------------------------------
% 0.19/0.43  % (5382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (5382)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (5382)Memory used [KB]: 6012
% 0.19/0.43  % (5382)Time elapsed: 0.004 s
% 0.19/0.43  % (5382)------------------------------
% 0.19/0.43  % (5382)------------------------------
% 0.19/0.43  % (5395)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.44  % (5375)Success in time 0.085 s
%------------------------------------------------------------------------------
