%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 112 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  131 ( 303 expanded)
%              Number of equality atoms :   40 ( 116 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f420,plain,(
    $false ),
    inference(subsumption_resolution,[],[f416,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f416,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f407,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f54,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | X1 = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f23,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f407,plain,(
    ! [X0] : r1_tarski(sK1,X0) ),
    inference(subsumption_resolution,[],[f404,f285])).

fof(f285,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f277,f18])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f277,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f275,f23])).

fof(f275,plain,(
    r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f271,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f271,plain,
    ( r1_tarski(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f244,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f72,f25])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f71,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f70,f19])).

fof(f70,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_xboole_0(X6)
      | ~ r2_hidden(X4,k2_zfmisc_1(X5,X6)) ) ),
    inference(resolution,[],[f48,f20])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f244,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(sK1,sK0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f241,f23])).

fof(f241,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | r1_tarski(sK1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | r1_tarski(sK1,sK0)
      | r1_tarski(sK1,sK0) ) ),
    inference(resolution,[],[f212,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f212,plain,(
    ! [X8,X9] :
      ( r1_tarski(sK0,X9)
      | r2_hidden(sK2(sK1,X8),sK0)
      | r1_tarski(sK1,X8) ) ),
    inference(resolution,[],[f107,f65])).

fof(f65,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X7,sK0) ) ),
    inference(superposition,[],[f39,f15])).

fof(f15,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK2(X2,X3)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X2,X3)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f87,f25])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,sK2(X2,X3)),k2_zfmisc_1(X1,X2))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f46,f25])).

fof(f46,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f404,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r1_tarski(sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r1_tarski(sK0,sK1)
      | r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f213,f26])).

fof(f213,plain,(
    ! [X10,X11] :
      ( r1_tarski(sK1,X10)
      | r2_hidden(sK2(sK0,X11),sK1)
      | r1_tarski(sK0,X11) ) ),
    inference(resolution,[],[f107,f62])).

fof(f62,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X6,sK1) ) ),
    inference(superposition,[],[f38,f15])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (27437)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (27451)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (27438)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (27443)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (27444)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (27437)Refutation not found, incomplete strategy% (27437)------------------------------
% 0.20/0.54  % (27437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27437)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27437)Memory used [KB]: 1663
% 0.20/0.54  % (27437)Time elapsed: 0.115 s
% 0.20/0.54  % (27437)------------------------------
% 0.20/0.54  % (27437)------------------------------
% 0.20/0.54  % (27446)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (27452)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.57  % (27439)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (27445)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.57  % (27462)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.57  % (27440)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.58  % (27457)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.58  % (27442)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.59  % (27453)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.59  % (27443)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f420,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(subsumption_resolution,[],[f416,f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    k1_xboole_0 != sK1),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,plain,(
% 0.20/0.59    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.20/0.59    inference(flattening,[],[f11])).
% 0.20/0.59  fof(f11,plain,(
% 0.20/0.59    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    inference(negated_conjecture,[],[f8])).
% 0.20/0.59  fof(f8,conjecture,(
% 0.20/0.59    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.20/0.59  fof(f416,plain,(
% 0.20/0.59    k1_xboole_0 = sK1),
% 0.20/0.59    inference(resolution,[],[f407,f55])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.59    inference(resolution,[],[f54,f19])).
% 0.20/0.59  fof(f19,plain,(
% 0.20/0.59    v1_xboole_0(k1_xboole_0)),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    v1_xboole_0(k1_xboole_0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ( ! [X2,X1] : (~v1_xboole_0(X2) | X1 = X2 | ~r1_tarski(X1,X2)) )),
% 0.20/0.59    inference(resolution,[],[f23,f50])).
% 0.20/0.59  fof(f50,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.59    inference(resolution,[],[f25,f20])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,plain,(
% 0.20/0.59    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.59  fof(f407,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(sK1,X0)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f404,f285])).
% 0.20/0.59  fof(f285,plain,(
% 0.20/0.59    ~r1_tarski(sK0,sK1)),
% 0.20/0.59    inference(subsumption_resolution,[],[f277,f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    sK0 != sK1),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f277,plain,(
% 0.20/0.59    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.20/0.59    inference(resolution,[],[f275,f23])).
% 0.20/0.59  fof(f275,plain,(
% 0.20/0.59    r1_tarski(sK1,sK0)),
% 0.20/0.59    inference(subsumption_resolution,[],[f271,f16])).
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    k1_xboole_0 != sK0),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f271,plain,(
% 0.20/0.59    r1_tarski(sK1,sK0) | k1_xboole_0 = sK0),
% 0.20/0.59    inference(resolution,[],[f244,f73])).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(resolution,[],[f72,f25])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f71,f43])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f29])).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 0.20/0.59    inference(resolution,[],[f70,f19])).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    ( ! [X6,X4,X5] : (~v1_xboole_0(X6) | ~r2_hidden(X4,k2_zfmisc_1(X5,X6))) )),
% 0.20/0.59    inference(resolution,[],[f48,f20])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.59    inference(equality_resolution,[],[f35])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.59  fof(f244,plain,(
% 0.20/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(sK1,sK0) | sK0 = X0) )),
% 0.20/0.59    inference(resolution,[],[f241,f23])).
% 0.20/0.59  fof(f241,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(sK0,X0) | r1_tarski(sK1,sK0)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f234])).
% 0.20/0.59  fof(f234,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(sK0,X0) | r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)) )),
% 0.20/0.59    inference(resolution,[],[f212,f26])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f212,plain,(
% 0.20/0.59    ( ! [X8,X9] : (r1_tarski(sK0,X9) | r2_hidden(sK2(sK1,X8),sK0) | r1_tarski(sK1,X8)) )),
% 0.20/0.59    inference(resolution,[],[f107,f65])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X7,sK0)) )),
% 0.20/0.59    inference(superposition,[],[f39,f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.20/0.59  fof(f107,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK2(X2,X3)),k2_zfmisc_1(X0,X2)) | r1_tarski(X2,X3) | r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(resolution,[],[f87,f25])).
% 0.20/0.59  fof(f87,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,sK2(X2,X3)),k2_zfmisc_1(X1,X2)) | r1_tarski(X2,X3)) )),
% 0.20/0.59    inference(resolution,[],[f46,f25])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X4,X0,X5,X1] : (~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 0.20/0.59    inference(equality_resolution,[],[f45])).
% 0.20/0.59  fof(f45,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.59    inference(equality_resolution,[],[f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f404,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | r1_tarski(sK0,sK1)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f397])).
% 0.20/0.59  fof(f397,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1)) )),
% 0.20/0.59    inference(resolution,[],[f213,f26])).
% 0.20/0.59  fof(f213,plain,(
% 0.20/0.59    ( ! [X10,X11] : (r1_tarski(sK1,X10) | r2_hidden(sK2(sK0,X11),sK1) | r1_tarski(sK0,X11)) )),
% 0.20/0.59    inference(resolution,[],[f107,f62])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X6,sK1)) )),
% 0.20/0.59    inference(superposition,[],[f38,f15])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f6])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (27443)------------------------------
% 0.20/0.59  % (27443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (27443)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (27443)Memory used [KB]: 6780
% 0.20/0.59  % (27443)Time elapsed: 0.115 s
% 0.20/0.59  % (27443)------------------------------
% 0.20/0.59  % (27443)------------------------------
% 0.20/0.59  % (27458)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.59  % (27441)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.59  % (27455)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.60  % (27448)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.60  % (27449)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.60  % (27456)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.60  % (27463)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.60  % (27465)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.60  % (27459)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.61  % (27447)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.61  % (27436)Success in time 0.243 s
%------------------------------------------------------------------------------
