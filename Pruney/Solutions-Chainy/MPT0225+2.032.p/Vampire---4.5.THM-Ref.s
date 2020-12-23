%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:10 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 111 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 199 expanded)
%              Number of equality atoms :   44 ( 113 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f114,f126])).

fof(f126,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f41,f118,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f118,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f116,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f116,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( sK0 != sK0
    | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f47,f55])).

fof(f55,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f47,plain,
    ( sK0 != sK1
    | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(inner_rewriting,[],[f32])).

fof(f32,plain,
    ( sK0 != sK1
    | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f14,f24,f24,f24])).

fof(f14,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f41,plain,(
    ! [X2] : r2_hidden(X2,k2_tarski(X2,X2)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_tarski(X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f114,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f78,f82,f20])).

fof(f82,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( sK0 != sK0
    | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | spl4_1 ),
    inference(backward_demodulation,[],[f47,f71])).

fof(f71,plain,
    ( sK0 = sK1
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f68,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f62,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f51,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_1
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f78,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))
    | spl4_1 ),
    inference(backward_demodulation,[],[f62,f71])).

fof(f56,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f31,f53,f49])).

fof(f31,plain,
    ( sK0 = sK1
    | k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f15,f24,f24,f24])).

fof(f15,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (789315584)
% 0.21/0.38  ipcrm: permission denied for id (789348358)
% 0.21/0.38  ipcrm: permission denied for id (789381127)
% 0.21/0.39  ipcrm: permission denied for id (789446668)
% 0.21/0.39  ipcrm: permission denied for id (789577746)
% 0.21/0.40  ipcrm: permission denied for id (789610515)
% 0.21/0.41  ipcrm: permission denied for id (789807137)
% 0.21/0.41  ipcrm: permission denied for id (789839906)
% 0.21/0.42  ipcrm: permission denied for id (789872675)
% 0.21/0.44  ipcrm: permission denied for id (790036535)
% 0.21/0.44  ipcrm: permission denied for id (790102073)
% 0.21/0.44  ipcrm: permission denied for id (790134843)
% 0.21/0.46  ipcrm: permission denied for id (790298698)
% 0.21/0.47  ipcrm: permission denied for id (790364237)
% 0.21/0.47  ipcrm: permission denied for id (790495314)
% 0.21/0.47  ipcrm: permission denied for id (790528083)
% 0.21/0.48  ipcrm: permission denied for id (790560852)
% 0.21/0.48  ipcrm: permission denied for id (790626389)
% 0.21/0.48  ipcrm: permission denied for id (790691929)
% 0.21/0.48  ipcrm: permission denied for id (790757467)
% 0.21/0.49  ipcrm: permission denied for id (790888542)
% 0.21/0.49  ipcrm: permission denied for id (790921311)
% 0.21/0.49  ipcrm: permission denied for id (790986851)
% 0.21/0.49  ipcrm: permission denied for id (791019620)
% 0.21/0.50  ipcrm: permission denied for id (791052389)
% 0.21/0.50  ipcrm: permission denied for id (791085159)
% 0.21/0.50  ipcrm: permission denied for id (791150699)
% 0.21/0.51  ipcrm: permission denied for id (791183469)
% 0.21/0.51  ipcrm: permission denied for id (791281777)
% 0.21/0.52  ipcrm: permission denied for id (791347319)
% 0.38/0.65  % (11769)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.38/0.66  % (11747)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.38/0.67  % (11760)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.38/0.67  % (11760)Refutation not found, incomplete strategy% (11760)------------------------------
% 0.38/0.67  % (11760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.67  % (11760)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.67  
% 0.38/0.67  % (11760)Memory used [KB]: 10618
% 0.38/0.67  % (11760)Time elapsed: 0.108 s
% 0.38/0.67  % (11760)------------------------------
% 0.38/0.67  % (11760)------------------------------
% 0.38/0.68  % (11754)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.38/0.68  % (11769)Refutation found. Thanks to Tanya!
% 0.38/0.68  % SZS status Theorem for theBenchmark
% 0.38/0.68  % SZS output start Proof for theBenchmark
% 0.38/0.68  fof(f127,plain,(
% 0.38/0.68    $false),
% 0.38/0.68    inference(avatar_sat_refutation,[],[f56,f114,f126])).
% 0.38/0.68  fof(f126,plain,(
% 0.38/0.68    ~spl4_2),
% 0.38/0.68    inference(avatar_contradiction_clause,[],[f122])).
% 0.38/0.68  fof(f122,plain,(
% 0.38/0.68    $false | ~spl4_2),
% 0.38/0.68    inference(unit_resulting_resolution,[],[f41,f118,f37])).
% 0.38/0.68  fof(f37,plain,(
% 0.38/0.68    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.38/0.68    inference(definition_unfolding,[],[f22,f24])).
% 0.38/0.68  fof(f24,plain,(
% 0.38/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.38/0.68    inference(cnf_transformation,[],[f5])).
% 0.38/0.68  fof(f5,axiom,(
% 0.38/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.38/0.68  fof(f22,plain,(
% 0.38/0.68    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.38/0.68    inference(cnf_transformation,[],[f12])).
% 0.38/0.68  fof(f12,plain,(
% 0.38/0.68    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.38/0.68    inference(ennf_transformation,[],[f7])).
% 0.38/0.68  fof(f7,axiom,(
% 0.38/0.68    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.38/0.68  fof(f118,plain,(
% 0.38/0.68    r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | ~spl4_2),
% 0.38/0.68    inference(unit_resulting_resolution,[],[f116,f20])).
% 0.38/0.68  fof(f20,plain,(
% 0.38/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.38/0.68    inference(cnf_transformation,[],[f2])).
% 0.38/0.68  fof(f2,axiom,(
% 0.38/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.38/0.68  fof(f116,plain,(
% 0.38/0.68    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | ~spl4_2),
% 0.38/0.68    inference(trivial_inequality_removal,[],[f115])).
% 0.38/0.68  fof(f115,plain,(
% 0.38/0.68    sK0 != sK0 | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | ~spl4_2),
% 0.38/0.68    inference(backward_demodulation,[],[f47,f55])).
% 0.38/0.68  fof(f55,plain,(
% 0.38/0.68    sK0 = sK1 | ~spl4_2),
% 0.38/0.68    inference(avatar_component_clause,[],[f53])).
% 0.38/0.68  fof(f53,plain,(
% 0.38/0.68    spl4_2 <=> sK0 = sK1),
% 0.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.38/0.68  fof(f47,plain,(
% 0.38/0.68    sK0 != sK1 | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 0.38/0.68    inference(inner_rewriting,[],[f32])).
% 0.38/0.68  fof(f32,plain,(
% 0.38/0.68    sK0 != sK1 | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.38/0.68    inference(definition_unfolding,[],[f14,f24,f24,f24])).
% 0.38/0.68  fof(f14,plain,(
% 0.38/0.68    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.38/0.68    inference(cnf_transformation,[],[f11])).
% 0.38/0.68  fof(f11,plain,(
% 0.38/0.68    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.38/0.68    inference(ennf_transformation,[],[f10])).
% 0.38/0.68  fof(f10,negated_conjecture,(
% 0.38/0.68    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.38/0.68    inference(negated_conjecture,[],[f9])).
% 0.38/0.68  fof(f9,conjecture,(
% 0.38/0.68    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.38/0.68  fof(f41,plain,(
% 0.38/0.68    ( ! [X2] : (r2_hidden(X2,k2_tarski(X2,X2))) )),
% 0.38/0.68    inference(equality_resolution,[],[f40])).
% 0.38/0.68  fof(f40,plain,(
% 0.38/0.68    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_tarski(X2,X2) != X1) )),
% 0.38/0.68    inference(equality_resolution,[],[f36])).
% 0.38/0.68  fof(f36,plain,(
% 0.38/0.68    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 0.38/0.68    inference(definition_unfolding,[],[f16,f24])).
% 0.38/0.68  fof(f16,plain,(
% 0.38/0.68    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.38/0.68    inference(cnf_transformation,[],[f3])).
% 0.38/0.68  fof(f3,axiom,(
% 0.38/0.68    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.38/0.68  fof(f114,plain,(
% 0.38/0.68    spl4_1),
% 0.38/0.68    inference(avatar_contradiction_clause,[],[f107])).
% 0.38/0.68  fof(f107,plain,(
% 0.38/0.68    $false | spl4_1),
% 0.38/0.68    inference(unit_resulting_resolution,[],[f78,f82,f20])).
% 0.38/0.68  fof(f82,plain,(
% 0.38/0.68    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | spl4_1),
% 0.38/0.68    inference(trivial_inequality_removal,[],[f81])).
% 0.38/0.68  fof(f81,plain,(
% 0.38/0.68    sK0 != sK0 | k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | spl4_1),
% 0.38/0.68    inference(backward_demodulation,[],[f47,f71])).
% 0.38/0.68  fof(f71,plain,(
% 0.38/0.68    sK0 = sK1 | spl4_1),
% 0.38/0.68    inference(unit_resulting_resolution,[],[f68,f39])).
% 0.38/0.68  fof(f39,plain,(
% 0.38/0.68    ( ! [X2,X0] : (~r2_hidden(X2,k2_tarski(X0,X0)) | X0 = X2) )),
% 0.38/0.68    inference(equality_resolution,[],[f35])).
% 0.38/0.68  fof(f35,plain,(
% 0.38/0.68    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 0.38/0.68    inference(definition_unfolding,[],[f17,f24])).
% 0.38/0.68  fof(f17,plain,(
% 0.38/0.68    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.38/0.68    inference(cnf_transformation,[],[f3])).
% 0.38/0.68  fof(f68,plain,(
% 0.38/0.68    r2_hidden(sK0,k2_tarski(sK1,sK1)) | spl4_1),
% 0.38/0.68    inference(unit_resulting_resolution,[],[f62,f38])).
% 0.38/0.68  fof(f38,plain,(
% 0.38/0.68    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.38/0.68    inference(definition_unfolding,[],[f23,f24])).
% 0.38/0.68  fof(f23,plain,(
% 0.38/0.68    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.38/0.68    inference(cnf_transformation,[],[f13])).
% 0.38/0.68  fof(f13,plain,(
% 0.38/0.68    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.38/0.68    inference(ennf_transformation,[],[f8])).
% 0.38/0.68  fof(f8,axiom,(
% 0.38/0.68    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.38/0.68  fof(f62,plain,(
% 0.38/0.68    ~r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) | spl4_1),
% 0.38/0.68    inference(unit_resulting_resolution,[],[f51,f21])).
% 0.38/0.68  fof(f21,plain,(
% 0.38/0.68    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.38/0.68    inference(cnf_transformation,[],[f2])).
% 0.38/0.68  fof(f51,plain,(
% 0.38/0.68    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) | spl4_1),
% 0.38/0.68    inference(avatar_component_clause,[],[f49])).
% 0.38/0.68  fof(f49,plain,(
% 0.38/0.68    spl4_1 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.38/0.68  fof(f78,plain,(
% 0.38/0.68    ~r1_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) | spl4_1),
% 0.38/0.68    inference(backward_demodulation,[],[f62,f71])).
% 0.38/0.68  fof(f56,plain,(
% 0.38/0.68    ~spl4_1 | spl4_2),
% 0.38/0.68    inference(avatar_split_clause,[],[f31,f53,f49])).
% 0.38/0.68  fof(f31,plain,(
% 0.38/0.68    sK0 = sK1 | k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 0.38/0.68    inference(definition_unfolding,[],[f15,f24,f24,f24])).
% 0.38/0.68  fof(f15,plain,(
% 0.38/0.68    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.38/0.68    inference(cnf_transformation,[],[f11])).
% 0.38/0.68  % SZS output end Proof for theBenchmark
% 0.38/0.68  % (11769)------------------------------
% 0.38/0.68  % (11769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (11769)Termination reason: Refutation
% 0.38/0.68  
% 0.38/0.68  % (11769)Memory used [KB]: 6268
% 0.38/0.68  % (11769)Time elapsed: 0.099 s
% 0.38/0.68  % (11769)------------------------------
% 0.38/0.68  % (11769)------------------------------
% 0.38/0.68  % (11588)Success in time 0.312 s
%------------------------------------------------------------------------------
