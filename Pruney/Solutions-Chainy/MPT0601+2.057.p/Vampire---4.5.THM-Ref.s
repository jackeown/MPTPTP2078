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
% DateTime   : Thu Dec  3 12:51:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  70 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 158 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f48,f80,f89])).

fof(f89,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f23,f86,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f86,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f84,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f84,plain,
    ( r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f20,f81,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f42,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f80,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f23,f62,f33])).

fof(f62,plain,
    ( r2_hidden(sK2(k1_xboole_0,k11_relat_1(sK1,sK0)),k1_xboole_0)
    | spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f46,f53,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f53,plain,
    ( ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK1,sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f20,f49,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f46,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f48,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f19,f44,f40])).

fof(f19,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f18,f44,f40])).

fof(f18,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.52  % (24609)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.53  % (24604)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (24625)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (24608)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (24606)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (24617)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (24607)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (24607)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f90,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(avatar_sat_refutation,[],[f47,f48,f80,f89])).
% 0.19/0.53  fof(f89,plain,(
% 0.19/0.53    ~spl6_1 | ~spl6_2),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f88])).
% 0.19/0.53  fof(f88,plain,(
% 0.19/0.53    $false | (~spl6_1 | ~spl6_2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f23,f86,f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.19/0.53    inference(definition_unfolding,[],[f31,f32])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,axiom,(
% 0.19/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.19/0.53  fof(f86,plain,(
% 0.19/0.53    r2_hidden(sK4(sK1,sK0),k1_xboole_0) | (~spl6_1 | ~spl6_2)),
% 0.19/0.53    inference(forward_demodulation,[],[f84,f45])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl6_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f44])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    spl6_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.53  fof(f84,plain,(
% 0.19/0.53    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0)) | ~spl6_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f20,f81,f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.19/0.53    inference(ennf_transformation,[],[f12])).
% 0.19/0.53  fof(f12,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.19/0.53  fof(f81,plain,(
% 0.19/0.53    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) | ~spl6_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f42,f35])).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.19/0.53    inference(equality_resolution,[],[f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl6_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f40])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    spl6_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    v1_relat_1(sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.19/0.53    inference(negated_conjecture,[],[f13])).
% 0.19/0.53  fof(f13,conjecture,(
% 0.19/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.53  fof(f80,plain,(
% 0.19/0.53    spl6_1 | spl6_2),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f79])).
% 0.19/0.53  fof(f79,plain,(
% 0.19/0.53    $false | (spl6_1 | spl6_2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f23,f62,f33])).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    r2_hidden(sK2(k1_xboole_0,k11_relat_1(sK1,sK0)),k1_xboole_0) | (spl6_1 | spl6_2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f46,f53,f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK0))) ) | spl6_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f20,f49,f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f16])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK1)) ) | spl6_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f41,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f26])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl6_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f40])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl6_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f44])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    ~spl6_1 | spl6_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f19,f44,f40])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    spl6_1 | ~spl6_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f18,f44,f40])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (24607)------------------------------
% 0.19/0.53  % (24607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (24607)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (24607)Memory used [KB]: 6268
% 0.19/0.53  % (24607)Time elapsed: 0.122 s
% 0.19/0.53  % (24607)------------------------------
% 0.19/0.53  % (24607)------------------------------
% 0.19/0.53  % (24625)Refutation not found, incomplete strategy% (24625)------------------------------
% 0.19/0.53  % (24625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (24603)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.54  % (24625)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (24625)Memory used [KB]: 10618
% 0.19/0.54  % (24625)Time elapsed: 0.119 s
% 0.19/0.54  % (24625)------------------------------
% 0.19/0.54  % (24625)------------------------------
% 0.19/0.54  % (24605)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.54  % (24632)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (24605)Refutation not found, incomplete strategy% (24605)------------------------------
% 0.19/0.54  % (24605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (24605)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (24605)Memory used [KB]: 10618
% 0.19/0.54  % (24605)Time elapsed: 0.131 s
% 0.19/0.54  % (24605)------------------------------
% 0.19/0.54  % (24605)------------------------------
% 0.19/0.54  % (24624)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.55  % (24622)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.55  % (24616)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.55  % (24619)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.55  % (24614)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (24615)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.56  % (24602)Success in time 0.2 s
%------------------------------------------------------------------------------
