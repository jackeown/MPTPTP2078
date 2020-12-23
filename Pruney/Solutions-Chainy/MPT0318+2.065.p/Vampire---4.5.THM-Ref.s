%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  91 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 160 expanded)
%              Number of equality atoms :   52 ( 104 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f51,f58,f77,f81])).

fof(f81,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f41,f56,f46,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f46,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f56,plain,
    ( k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_4
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | spl2_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f77,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f37,f68,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f26])).

% (6399)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f15,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f68,plain,
    ( ! [X5] : r2_hidden(sK1,X5)
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k1_xboole_0
        | r2_hidden(sK1,X5) )
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f63,f13])).

fof(f13,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f63,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X5)
        | r2_hidden(sK1,X5) )
    | ~ spl2_4 ),
    inference(superposition,[],[f34,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,
    ( spl2_4
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f53,f48,f39,f55])).

fof(f48,plain,
    ( spl2_3
  <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f16,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f28,f48,f44])).

fof(f28,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f11,f27,f27])).

fof(f11,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f42,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f12,f39])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:37:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (6385)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (6393)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (6383)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (6377)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (6393)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f42,f51,f58,f77,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl2_1 | ~spl2_2 | spl2_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    $false | (spl2_1 | ~spl2_2 | spl2_4)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f41,f56,f46,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl2_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl2_4 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    spl2_1 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ~spl2_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    $false | ~spl2_4),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f37,f68,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f20,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f14,f26])).
% 0.22/0.51  % (6399)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f15,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X5] : (r2_hidden(sK1,X5)) ) | ~spl2_4),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(sK1,X5)) ) | ~spl2_4),
% 0.22/0.51    inference(forward_demodulation,[],[f63,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X5] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X5) | r2_hidden(sK1,X5)) ) | ~spl2_4),
% 0.22/0.51    inference(superposition,[],[f34,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f23,f26])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.22/0.51    inference(equality_resolution,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f21,f27])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl2_4 | spl2_1 | ~spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f48,f39,f55])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl2_3 <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_3),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl2_3),
% 0.22/0.51    inference(superposition,[],[f16,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f48])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl2_2 | spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f48,f44])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.51    inference(definition_unfolding,[],[f11,f27,f27])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f12,f39])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (6393)------------------------------
% 0.22/0.51  % (6393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6393)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (6393)Memory used [KB]: 10746
% 0.22/0.51  % (6393)Time elapsed: 0.049 s
% 0.22/0.51  % (6393)------------------------------
% 0.22/0.51  % (6393)------------------------------
% 0.22/0.52  % (6370)Success in time 0.152 s
%------------------------------------------------------------------------------
