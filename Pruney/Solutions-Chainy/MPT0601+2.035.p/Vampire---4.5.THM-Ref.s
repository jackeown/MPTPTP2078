%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  83 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  114 ( 198 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f45,f134,f144])).

fof(f144,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f50,f51])).

fof(f51,plain,
    ( ~ v1_relat_1(k11_relat_1(sK1,sK0))
    | spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f43,f48,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f48,plain,
    ( ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK1,sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f18,f46,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f46,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f38,f34])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f38,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl10_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f43,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl10_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f50,plain,
    ( v1_relat_1(k11_relat_1(sK1,sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f48,f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f134,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f25,f129,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f129,plain,
    ( r2_hidden(sK8(sK1,sK0),k1_xboole_0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f123,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f123,plain,
    ( r2_hidden(sK8(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f18,f106,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f106,plain,
    ( r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1)
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

% (2977)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f45,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f17,f41,f37])).

fof(f17,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f16,f41,f37])).

fof(f16,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:22:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (2965)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (2976)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (2969)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (2969)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f44,f45,f134,f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl10_1 | spl10_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    $false | (spl10_1 | spl10_2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f50,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ~v1_relat_1(k11_relat_1(sK1,sK0)) | (spl10_1 | spl10_2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f43,f48,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK0))) ) | spl10_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f18,f46,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK1)) ) | spl10_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f38,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl10_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    spl10_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl10_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    spl10_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    v1_relat_1(k11_relat_1(sK1,sK0)) | spl10_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f48,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ~spl10_1 | ~spl10_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f132])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    $false | (~spl10_1 | ~spl10_2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f25,f129,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f30,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    r2_hidden(sK8(sK1,sK0),k1_xboole_0) | (~spl10_1 | ~spl10_2)),
% 0.20/0.52    inference(forward_demodulation,[],[f123,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl10_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f41])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    r2_hidden(sK8(sK1,sK0),k11_relat_1(sK1,sK0)) | ~spl10_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f18,f106,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK0,sK8(sK1,sK0)),sK1) | ~spl10_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f39,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl10_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f37])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  % (2977)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ~spl10_1 | spl10_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f17,f41,f37])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    spl10_1 | ~spl10_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f16,f41,f37])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (2969)------------------------------
% 0.20/0.52  % (2969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2969)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (2969)Memory used [KB]: 6268
% 0.20/0.52  % (2969)Time elapsed: 0.109 s
% 0.20/0.52  % (2969)------------------------------
% 0.20/0.52  % (2969)------------------------------
% 0.20/0.52  % (2966)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (2981)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (2963)Success in time 0.162 s
%------------------------------------------------------------------------------
