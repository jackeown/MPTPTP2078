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
% DateTime   : Thu Dec  3 12:47:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 162 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   20
%              Number of atoms          :  105 ( 287 expanded)
%              Number of equality atoms :   35 (  93 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(subsumption_resolution,[],[f254,f19])).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f254,plain,(
    ~ r1_xboole_0(k2_enumset1(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0)))),k1_xboole_0) ),
    inference(resolution,[],[f247,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f247,plain,(
    r2_hidden(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0) ),
    inference(resolution,[],[f244,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f244,plain,(
    r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f241,f187])).

fof(f187,plain,(
    k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f17,f141])).

fof(f141,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f140,f19])).

fof(f140,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ r1_xboole_0(k2_enumset1(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0)))),k1_xboole_0) ),
    inference(resolution,[],[f137,f32])).

fof(f137,plain,
    ( r2_hidden(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f136,f33])).

fof(f136,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f135,f18])).

fof(f18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k2_relat_1(X0) ) ),
    inference(resolution,[],[f128,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f128,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | k1_relat_1(k1_xboole_0) = k2_relat_1(X3)
      | r2_hidden(sK0(X3),k1_relat_1(X3)) ) ),
    inference(resolution,[],[f125,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK0(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f125,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_xboole_0,X0),X0)
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f36,f19])).

fof(f36,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k2_enumset1(k4_tarski(sK1(X2,X3),sK3(X2,X3)),k4_tarski(sK1(X2,X3),sK3(X2,X3)),k4_tarski(sK1(X2,X3),sK3(X2,X3)),k4_tarski(sK1(X2,X3),sK3(X2,X3))),X2)
      | k1_relat_1(X2) = X3
      | r2_hidden(sK1(X2,X3),X3) ) ),
    inference(resolution,[],[f26,f32])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f241,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f239,f193])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f192,f18])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f186,f21])).

fof(f186,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f23,f141])).

fof(f239,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_relat_1(X0))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f40,f19])).

fof(f40,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(k2_enumset1(sK1(X3,X4),sK1(X3,X4),sK1(X3,X4),sK1(X3,X4)),X4)
      | k1_relat_1(X3) = X4
      | r2_hidden(sK1(X3,X4),k1_relat_1(X3)) ) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:06:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (20123)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (20125)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (20117)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (20116)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (20108)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (20117)Refutation not found, incomplete strategy% (20117)------------------------------
% 0.20/0.52  % (20117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20125)Refutation not found, incomplete strategy% (20125)------------------------------
% 0.20/0.52  % (20125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20117)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20117)Memory used [KB]: 6140
% 0.20/0.52  % (20117)Time elapsed: 0.005 s
% 0.20/0.52  % (20117)------------------------------
% 0.20/0.52  % (20117)------------------------------
% 0.20/0.52  % (20125)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20125)Memory used [KB]: 1663
% 0.20/0.52  % (20125)Time elapsed: 0.059 s
% 0.20/0.52  % (20125)------------------------------
% 0.20/0.52  % (20125)------------------------------
% 0.20/0.52  % (20109)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (20108)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (20114)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (20123)Refutation not found, incomplete strategy% (20123)------------------------------
% 0.20/0.52  % (20123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20123)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20123)Memory used [KB]: 1663
% 0.20/0.53  % (20123)Time elapsed: 0.105 s
% 0.20/0.53  % (20123)------------------------------
% 0.20/0.53  % (20123)------------------------------
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f254,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.53  fof(f254,plain,(
% 0.20/0.53    ~r1_xboole_0(k2_enumset1(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0)))),k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f247,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f28,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f20,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f22,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f244,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK2(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(subsumption_resolution,[],[f241,f187])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f185])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f17,f141])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f140,f19])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) | ~r1_xboole_0(k2_enumset1(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0)))),k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f137,f32])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK0(k1_xboole_0),sK2(k1_xboole_0,sK0(k1_xboole_0))),k1_xboole_0) | k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f136,f33])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f135,f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k2_relat_1(X0)) )),
% 0.20/0.53    inference(resolution,[],[f128,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X3] : (~v1_relat_1(X3) | k1_relat_1(k1_xboole_0) = k2_relat_1(X3) | r2_hidden(sK0(X3),k1_relat_1(X3))) )),
% 0.20/0.53    inference(resolution,[],[f125,f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | r2_hidden(sK0(X1),k1_relat_1(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK1(k1_xboole_0,X0),X0) | k1_relat_1(k1_xboole_0) = X0) )),
% 0.20/0.53    inference(resolution,[],[f36,f19])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r1_xboole_0(k2_enumset1(k4_tarski(sK1(X2,X3),sK3(X2,X3)),k4_tarski(sK1(X2,X3),sK3(X2,X3)),k4_tarski(sK1(X2,X3),sK3(X2,X3)),k4_tarski(sK1(X2,X3),sK3(X2,X3))),X2) | k1_relat_1(X2) = X3 | r2_hidden(sK1(X2,X3),X3)) )),
% 0.20/0.53    inference(resolution,[],[f26,f32])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,negated_conjecture,(
% 0.20/0.53    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(negated_conjecture,[],[f10])).
% 0.20/0.53  fof(f10,conjecture,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(resolution,[],[f239,f193])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f192,f18])).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.20/0.53    inference(resolution,[],[f186,f21])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))) )),
% 0.20/0.53    inference(superposition,[],[f23,f141])).
% 0.20/0.53  fof(f239,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_relat_1(X0)) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.20/0.53    inference(resolution,[],[f40,f19])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X4,X3] : (~r1_xboole_0(k2_enumset1(sK1(X3,X4),sK1(X3,X4),sK1(X3,X4),sK1(X3,X4)),X4) | k1_relat_1(X3) = X4 | r2_hidden(sK1(X3,X4),k1_relat_1(X3))) )),
% 0.20/0.53    inference(resolution,[],[f35,f32])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) = X1) )),
% 0.20/0.53    inference(resolution,[],[f26,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.53    inference(equality_resolution,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (20108)------------------------------
% 0.20/0.53  % (20108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20108)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (20108)Memory used [KB]: 6396
% 0.20/0.53  % (20108)Time elapsed: 0.108 s
% 0.20/0.53  % (20108)------------------------------
% 0.20/0.53  % (20108)------------------------------
% 1.34/0.54  % (20101)Success in time 0.17 s
%------------------------------------------------------------------------------
