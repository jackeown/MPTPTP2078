%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 125 expanded)
%              Number of leaves         :   10 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 284 expanded)
%              Number of equality atoms :   40 (  92 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f29,f34,f42,f52,f61,f63,f64,f66,f71])).

fof(f71,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f70,f24,f50])).

fof(f50,plain,
    ( spl2_5
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f24,plain,
    ( spl2_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f70,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f67,f25])).

fof(f25,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | k1_xboole_0 = k9_relat_1(sK1,k1_tarski(X0)) ) ),
    inference(resolution,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
      | k1_xboole_0 = k9_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f14,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k9_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f47,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0))
      | k1_xboole_0 != k11_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f46,f12])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f15,f43])).

fof(f43,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0)) ),
    inference(resolution,[],[f13,f12])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,
    ( spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f65,f50,f40])).

fof(f40,plain,
    ( spl2_4
  <=> r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f65,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f56,f12])).

fof(f56,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(superposition,[],[f15,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f45,f40,f32])).

fof(f32,plain,
    ( spl2_3
  <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f45,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f41,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f41,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f63,plain,
    ( spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f53,f50,f24])).

fof(f53,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f51,f43])).

fof(f61,plain,
    ( ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f38,f32,f21])).

% (14380)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
fof(f21,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f38,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f35])).

fof(f35,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(superposition,[],[f19,f33])).

fof(f33,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f52,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f48,f40,f50])).

fof(f48,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f44,f41])).

fof(f42,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f37,f32,f40])).

fof(f37,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_3 ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | ~ spl2_3 ),
    inference(superposition,[],[f16,f33])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,
    ( spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f30,f21,f32])).

fof(f30,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))
    | spl2_1 ),
    inference(resolution,[],[f18,f22])).

fof(f22,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f10,f24,f21])).

fof(f10,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f11,f24,f21])).

fof(f11,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:53:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (14381)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (14382)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (14379)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.44  % (14379)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f26,f29,f34,f42,f52,f61,f63,f64,f66,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl2_5 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f70,f24,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl2_5 <=> k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    spl2_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0)) | ~spl2_2),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0)) | ~spl2_2),
% 0.21/0.44    inference(superposition,[],[f67,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f24])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | k1_xboole_0 = k9_relat_1(sK1,k1_tarski(X0))) )),
% 0.21/0.44    inference(resolution,[],[f47,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 = k9_relat_1(sK1,X0)) )),
% 0.21/0.44    inference(resolution,[],[f14,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) = k1_xboole_0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)) | k1_xboole_0 != k11_relat_1(sK1,X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f46,f12])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k1_tarski(X0)) | ~v1_relat_1(sK1)) )),
% 0.21/0.44    inference(superposition,[],[f15,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))) )),
% 0.21/0.44    inference(resolution,[],[f13,f12])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k9_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    spl2_4 | ~spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f65,f50,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    spl2_4 <=> r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~spl2_5),
% 0.21/0.44    inference(subsumption_resolution,[],[f56,f12])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl2_5),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl2_5),
% 0.21/0.44    inference(superposition,[],[f15,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0)) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f50])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl2_3 | ~spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f45,f40,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl2_3 <=> k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~spl2_4),
% 0.21/0.44    inference(resolution,[],[f41,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f40])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl2_2 | ~spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f53,f50,f24])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl2_5),
% 0.21/0.44    inference(superposition,[],[f51,f43])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ~spl2_1 | ~spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f38,f32,f21])).
% 0.21/0.44  % (14380)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    spl2_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    k1_relat_1(sK1) != k1_relat_1(sK1) | ~r2_hidden(sK0,k1_relat_1(sK1)) | ~spl2_3),
% 0.21/0.44    inference(superposition,[],[f19,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    spl2_5 | ~spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f40,f50])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    k1_xboole_0 = k9_relat_1(sK1,k1_tarski(sK0)) | ~spl2_4),
% 0.21/0.44    inference(resolution,[],[f44,f41])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl2_4 | ~spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f32,f40])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~spl2_3),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    k1_relat_1(sK1) != k1_relat_1(sK1) | r1_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | ~spl2_3),
% 0.21/0.44    inference(superposition,[],[f16,f33])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    spl2_3 | spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f21,f32])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k1_tarski(sK0)) | spl2_1),
% 0.21/0.44    inference(resolution,[],[f18,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f21])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    spl2_1 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f10,f24,f21])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ~spl2_1 | spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f11,f24,f21])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (14379)------------------------------
% 0.21/0.44  % (14379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (14379)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (14379)Memory used [KB]: 10618
% 0.21/0.44  % (14379)Time elapsed: 0.006 s
% 0.21/0.44  % (14379)------------------------------
% 0.21/0.44  % (14379)------------------------------
% 0.21/0.44  % (14375)Success in time 0.076 s
%------------------------------------------------------------------------------
