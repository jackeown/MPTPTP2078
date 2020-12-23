%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:50 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   55 (  95 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 180 expanded)
%              Number of equality atoms :   32 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f55,f59,f64,f70,f75])).

fof(f75,plain,
    ( ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f73,f32])).

fof(f32,plain,(
    sK1 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f18,f29,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f18,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f73,plain,
    ( sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f69,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_7
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f70,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f65,f62,f40,f67])).

fof(f40,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f62,plain,
    ( spl2_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f65,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f63,f42])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f60,f57,f40,f62])).

fof(f57,plain,
    ( spl2_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) )
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f35,f57])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f55,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f38,f53])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f23,f29,f21,f29])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

% (10106)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f29,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:07:01 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.43  % (10103)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.18/0.43  % (10107)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.43  % (10107)Refutation not found, incomplete strategy% (10107)------------------------------
% 0.18/0.43  % (10107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.43  % (10107)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.43  
% 0.18/0.43  % (10107)Memory used [KB]: 10490
% 0.18/0.43  % (10107)Time elapsed: 0.046 s
% 0.18/0.43  % (10107)------------------------------
% 0.18/0.43  % (10107)------------------------------
% 0.18/0.43  % (10096)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.18/0.44  % (10112)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.18/0.44  % (10100)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.44  % (10103)Refutation found. Thanks to Tanya!
% 0.18/0.44  % SZS status Theorem for theBenchmark
% 0.18/0.44  % SZS output start Proof for theBenchmark
% 0.18/0.44  fof(f76,plain,(
% 0.18/0.44    $false),
% 0.18/0.44    inference(avatar_sat_refutation,[],[f43,f55,f59,f64,f70,f75])).
% 0.18/0.44  fof(f75,plain,(
% 0.18/0.44    ~spl2_4 | ~spl2_7),
% 0.18/0.44    inference(avatar_contradiction_clause,[],[f74])).
% 0.18/0.44  fof(f74,plain,(
% 0.18/0.44    $false | (~spl2_4 | ~spl2_7)),
% 0.18/0.44    inference(subsumption_resolution,[],[f73,f32])).
% 0.18/0.44  fof(f32,plain,(
% 0.18/0.44    sK1 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.18/0.44    inference(definition_unfolding,[],[f18,f29,f31])).
% 0.18/0.44  fof(f31,plain,(
% 0.18/0.44    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.44    inference(definition_unfolding,[],[f19,f30])).
% 0.18/0.44  fof(f30,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.44    inference(definition_unfolding,[],[f20,f25])).
% 0.18/0.44  fof(f25,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f7])).
% 0.18/0.44  fof(f7,axiom,(
% 0.18/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.44  fof(f20,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f6])).
% 0.18/0.44  fof(f6,axiom,(
% 0.18/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.44  fof(f19,plain,(
% 0.18/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f5])).
% 0.18/0.44  fof(f5,axiom,(
% 0.18/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.44  fof(f29,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.18/0.44    inference(definition_unfolding,[],[f22,f21])).
% 0.18/0.44  fof(f21,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.44    inference(cnf_transformation,[],[f1])).
% 0.18/0.44  fof(f1,axiom,(
% 0.18/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.44  fof(f22,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.18/0.44    inference(cnf_transformation,[],[f4])).
% 0.18/0.44  fof(f4,axiom,(
% 0.18/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.18/0.44  fof(f18,plain,(
% 0.18/0.44    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f14])).
% 0.18/0.44  fof(f14,plain,(
% 0.18/0.44    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).
% 0.18/0.44  fof(f13,plain,(
% 0.18/0.44    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f11,plain,(
% 0.18/0.44    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.18/0.44    inference(ennf_transformation,[],[f10])).
% 0.18/0.44  fof(f10,negated_conjecture,(
% 0.18/0.44    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.18/0.44    inference(negated_conjecture,[],[f9])).
% 0.18/0.44  fof(f9,conjecture,(
% 0.18/0.44    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.18/0.44  fof(f73,plain,(
% 0.18/0.44    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) | (~spl2_4 | ~spl2_7)),
% 0.18/0.44    inference(resolution,[],[f69,f54])).
% 0.18/0.44  fof(f54,plain,(
% 0.18/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) ) | ~spl2_4),
% 0.18/0.44    inference(avatar_component_clause,[],[f53])).
% 0.18/0.44  fof(f53,plain,(
% 0.18/0.44    spl2_4 <=> ! [X1,X0] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.18/0.44  fof(f69,plain,(
% 0.18/0.44    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_7),
% 0.18/0.44    inference(avatar_component_clause,[],[f67])).
% 0.18/0.44  fof(f67,plain,(
% 0.18/0.44    spl2_7 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.18/0.44  fof(f70,plain,(
% 0.18/0.44    spl2_7 | ~spl2_1 | ~spl2_6),
% 0.18/0.44    inference(avatar_split_clause,[],[f65,f62,f40,f67])).
% 0.18/0.44  fof(f40,plain,(
% 0.18/0.44    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.18/0.44  fof(f62,plain,(
% 0.18/0.44    spl2_6 <=> ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1))),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.18/0.44  fof(f65,plain,(
% 0.18/0.44    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl2_1 | ~spl2_6)),
% 0.18/0.44    inference(resolution,[],[f63,f42])).
% 0.18/0.44  fof(f42,plain,(
% 0.18/0.44    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.18/0.44    inference(avatar_component_clause,[],[f40])).
% 0.18/0.44  fof(f63,plain,(
% 0.18/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1)) ) | ~spl2_6),
% 0.18/0.44    inference(avatar_component_clause,[],[f62])).
% 0.18/0.44  fof(f64,plain,(
% 0.18/0.44    spl2_6 | ~spl2_1 | ~spl2_5),
% 0.18/0.44    inference(avatar_split_clause,[],[f60,f57,f40,f62])).
% 0.18/0.44  fof(f57,plain,(
% 0.18/0.44    spl2_5 <=> ! [X1,X0,X2] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.18/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.18/0.44  fof(f60,plain,(
% 0.18/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1)) ) | (~spl2_1 | ~spl2_5)),
% 0.18/0.44    inference(resolution,[],[f58,f42])).
% 0.18/0.44  fof(f58,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) ) | ~spl2_5),
% 0.18/0.44    inference(avatar_component_clause,[],[f57])).
% 0.18/0.44  fof(f59,plain,(
% 0.18/0.44    spl2_5),
% 0.18/0.44    inference(avatar_split_clause,[],[f35,f57])).
% 0.18/0.44  fof(f35,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.18/0.44    inference(definition_unfolding,[],[f28,f30])).
% 0.18/0.44  fof(f28,plain,(
% 0.18/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f16])).
% 0.18/0.44  fof(f16,plain,(
% 0.18/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.18/0.44    inference(flattening,[],[f15])).
% 0.18/0.44  fof(f15,plain,(
% 0.18/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.18/0.44    inference(nnf_transformation,[],[f8])).
% 0.18/0.44  fof(f8,axiom,(
% 0.18/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.18/0.44  fof(f55,plain,(
% 0.18/0.44    spl2_4),
% 0.18/0.44    inference(avatar_split_clause,[],[f38,f53])).
% 0.18/0.44  fof(f38,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.44    inference(forward_demodulation,[],[f34,f33])).
% 0.18/0.44  fof(f33,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 0.18/0.44    inference(definition_unfolding,[],[f23,f29,f21,f29])).
% 0.18/0.44  fof(f23,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f2])).
% 0.18/0.44  % (10106)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.44  fof(f2,axiom,(
% 0.18/0.44    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.18/0.44  fof(f34,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.44    inference(definition_unfolding,[],[f24,f29,f21])).
% 0.18/0.44  fof(f24,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f12])).
% 0.18/0.44  fof(f12,plain,(
% 0.18/0.44    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.44    inference(ennf_transformation,[],[f3])).
% 0.18/0.44  fof(f3,axiom,(
% 0.18/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.18/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.18/0.44  fof(f43,plain,(
% 0.18/0.44    spl2_1),
% 0.18/0.44    inference(avatar_split_clause,[],[f17,f40])).
% 0.18/0.44  fof(f17,plain,(
% 0.18/0.44    r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f14])).
% 0.18/0.44  % SZS output end Proof for theBenchmark
% 0.18/0.44  % (10103)------------------------------
% 0.18/0.44  % (10103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (10103)Termination reason: Refutation
% 0.18/0.44  
% 0.18/0.44  % (10103)Memory used [KB]: 6140
% 0.18/0.44  % (10103)Time elapsed: 0.063 s
% 0.18/0.44  % (10103)------------------------------
% 0.18/0.44  % (10103)------------------------------
% 0.18/0.45  % (10099)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.45  % (10093)Success in time 0.109 s
%------------------------------------------------------------------------------
