%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  97 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 159 expanded)
%              Number of equality atoms :   60 ( 116 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f47,f54,f64,f69,f73])).

fof(f73,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f37,f52,f42,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f42,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f37,plain,
    ( k1_xboole_0 != sK0
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f69,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f15,f63])).

fof(f63,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_5
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f15,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f64,plain,
    ( ~ spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f59,f51,f61])).

fof(f59,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f58,f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f58,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(superposition,[],[f33,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f33,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ) ),
    inference(definition_unfolding,[],[f24,f27,f19,f27,f27])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f54,plain,
    ( spl2_4
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f49,f44,f35,f51])).

fof(f44,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f20,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f47,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f28,f44,f40])).

fof(f28,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f13,f27,f27])).

fof(f13,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f35])).

fof(f14,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (5251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (5233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (5242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (5234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (5241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5251)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f38,f47,f54,f64,f69,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl2_1 | ~spl2_2 | spl2_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    $false | (spl2_1 | ~spl2_2 | spl2_4)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f37,f52,f42,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl2_4 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    spl2_1 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl2_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    $false | spl2_5),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f15,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl2_5 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~spl2_5 | ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f59,f51,f61])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_4),
% 0.21/0.52    inference(forward_demodulation,[],[f58,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.52    inference(rectify,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl2_4),
% 0.21/0.52    inference(superposition,[],[f33,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f27,f19,f27,f27])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f16,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl2_4 | spl2_1 | ~spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f49,f44,f35,f51])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl2_3 <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_3),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_3),
% 0.21/0.52    inference(superposition,[],[f20,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl2_2 | spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f44,f40])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(definition_unfolding,[],[f13,f27,f27])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f14,f35])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (5251)------------------------------
% 0.21/0.53  % (5251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5251)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (5251)Memory used [KB]: 10746
% 0.21/0.53  % (5251)Time elapsed: 0.071 s
% 0.21/0.53  % (5251)------------------------------
% 0.21/0.53  % (5251)------------------------------
% 0.21/0.53  % (5223)Success in time 0.163 s
%------------------------------------------------------------------------------
