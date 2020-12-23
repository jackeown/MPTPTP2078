%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:05 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  77 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f18])).

fof(f18,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f9,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f35,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f34,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f29,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f33,f20])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f33,plain,(
    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f32,f21])).

fof(f21,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f23,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (804749313)
% 0.13/0.37  ipcrm: permission denied for id (804814851)
% 0.13/0.37  ipcrm: permission denied for id (804880390)
% 0.13/0.37  ipcrm: permission denied for id (804913159)
% 0.13/0.38  ipcrm: permission denied for id (804978701)
% 0.13/0.38  ipcrm: permission denied for id (805011471)
% 0.21/0.40  ipcrm: permission denied for id (805109793)
% 0.21/0.42  ipcrm: permission denied for id (805208109)
% 0.21/0.43  ipcrm: permission denied for id (805339190)
% 0.21/0.44  ipcrm: permission denied for id (805470268)
% 0.21/0.44  ipcrm: permission denied for id (805503037)
% 0.21/0.44  ipcrm: permission denied for id (805568575)
% 0.21/0.44  ipcrm: permission denied for id (805601345)
% 0.21/0.46  ipcrm: permission denied for id (805765204)
% 0.21/0.47  ipcrm: permission denied for id (805797976)
% 0.21/0.50  ipcrm: permission denied for id (805929074)
% 0.21/0.51  ipcrm: permission denied for id (805994620)
% 0.21/0.52  ipcrm: permission denied for id (806027390)
% 0.38/0.64  % (7224)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.38/0.65  % (7238)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.38/0.65  % (7231)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.38/0.66  % (7231)Refutation not found, incomplete strategy% (7231)------------------------------
% 0.38/0.66  % (7231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (7231)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (7231)Memory used [KB]: 10618
% 0.38/0.66  % (7231)Time elapsed: 0.096 s
% 0.38/0.66  % (7231)------------------------------
% 0.38/0.66  % (7231)------------------------------
% 0.38/0.66  % (7238)Refutation not found, incomplete strategy% (7238)------------------------------
% 0.38/0.66  % (7238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (7238)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (7238)Memory used [KB]: 6140
% 0.38/0.66  % (7238)Time elapsed: 0.002 s
% 0.38/0.66  % (7238)------------------------------
% 0.38/0.66  % (7238)------------------------------
% 0.38/0.67  % (7223)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.38/0.68  % (7227)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.38/0.68  % (7227)Refutation not found, incomplete strategy% (7227)------------------------------
% 0.38/0.68  % (7227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (7227)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.68  
% 0.38/0.68  % (7227)Memory used [KB]: 6140
% 0.38/0.68  % (7227)Time elapsed: 0.111 s
% 0.38/0.68  % (7227)------------------------------
% 0.38/0.68  % (7227)------------------------------
% 0.38/0.68  % (7230)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.38/0.68  % (7223)Refutation not found, incomplete strategy% (7223)------------------------------
% 0.38/0.68  % (7223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (7223)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.68  
% 0.38/0.68  % (7223)Memory used [KB]: 1663
% 0.38/0.68  % (7223)Time elapsed: 0.100 s
% 0.38/0.68  % (7223)------------------------------
% 0.38/0.68  % (7223)------------------------------
% 0.56/0.69  % (7243)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.56/0.69  % (7230)Refutation found. Thanks to Tanya!
% 0.56/0.69  % SZS status Theorem for theBenchmark
% 0.56/0.69  % SZS output start Proof for theBenchmark
% 0.56/0.69  fof(f36,plain,(
% 0.56/0.69    $false),
% 0.56/0.69    inference(subsumption_resolution,[],[f35,f18])).
% 0.56/0.69  fof(f18,plain,(
% 0.56/0.69    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.56/0.69    inference(cnf_transformation,[],[f10])).
% 0.56/0.69  fof(f10,plain,(
% 0.56/0.69    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.56/0.69    inference(flattening,[],[f9])).
% 0.56/0.69  fof(f9,negated_conjecture,(
% 0.56/0.69    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.56/0.69    inference(negated_conjecture,[],[f8])).
% 0.56/0.69  fof(f8,conjecture,(
% 0.56/0.69    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.56/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.56/0.69  fof(f35,plain,(
% 0.56/0.69    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.56/0.69    inference(forward_demodulation,[],[f34,f30])).
% 0.56/0.69  fof(f30,plain,(
% 0.56/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.56/0.69    inference(resolution,[],[f29,f25])).
% 0.56/0.69  fof(f25,plain,(
% 0.56/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.56/0.69    inference(cnf_transformation,[],[f14])).
% 0.56/0.69  fof(f14,plain,(
% 0.56/0.69    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.56/0.69    inference(ennf_transformation,[],[f3])).
% 0.56/0.69  fof(f3,axiom,(
% 0.56/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.56/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.56/0.69  fof(f29,plain,(
% 0.56/0.69    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.56/0.69    inference(duplicate_literal_removal,[],[f28])).
% 0.56/0.69  fof(f28,plain,(
% 0.56/0.69    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.56/0.69    inference(resolution,[],[f27,f26])).
% 0.56/0.69  fof(f26,plain,(
% 0.56/0.69    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.56/0.69    inference(cnf_transformation,[],[f17])).
% 0.56/0.69  fof(f17,plain,(
% 0.56/0.69    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.56/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 0.56/0.69  fof(f16,plain,(
% 0.56/0.69    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.56/0.69    introduced(choice_axiom,[])).
% 0.56/0.69  fof(f15,plain,(
% 0.56/0.69    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.56/0.69    inference(ennf_transformation,[],[f11])).
% 0.56/0.69  fof(f11,plain,(
% 0.56/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.56/0.69    inference(unused_predicate_definition_removal,[],[f1])).
% 0.56/0.69  fof(f1,axiom,(
% 0.56/0.69    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.56/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.56/0.69  fof(f27,plain,(
% 0.56/0.69    ( ! [X0,X1] : (~r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.56/0.69    inference(cnf_transformation,[],[f17])).
% 0.56/0.69  fof(f34,plain,(
% 0.56/0.69    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.56/0.69    inference(forward_demodulation,[],[f33,f20])).
% 0.56/0.69  fof(f20,plain,(
% 0.56/0.69    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.56/0.69    inference(cnf_transformation,[],[f7])).
% 0.56/0.69  fof(f7,axiom,(
% 0.56/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.56/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.56/0.69  fof(f33,plain,(
% 0.56/0.69    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.56/0.69    inference(forward_demodulation,[],[f32,f21])).
% 0.56/0.69  fof(f21,plain,(
% 0.56/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.56/0.69    inference(cnf_transformation,[],[f7])).
% 0.56/0.69  fof(f32,plain,(
% 0.56/0.69    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.56/0.69    inference(resolution,[],[f31,f19])).
% 0.56/0.69  fof(f19,plain,(
% 0.56/0.69    v1_xboole_0(k1_xboole_0)),
% 0.56/0.69    inference(cnf_transformation,[],[f2])).
% 0.56/0.69  fof(f2,axiom,(
% 0.56/0.69    v1_xboole_0(k1_xboole_0)),
% 0.56/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.56/0.69  fof(f31,plain,(
% 0.56/0.69    ( ! [X0] : (~v1_xboole_0(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.56/0.69    inference(resolution,[],[f23,f22])).
% 0.56/0.69  fof(f22,plain,(
% 0.56/0.69    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.56/0.69    inference(cnf_transformation,[],[f12])).
% 0.56/0.69  fof(f12,plain,(
% 0.56/0.69    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.56/0.69    inference(ennf_transformation,[],[f5])).
% 0.56/0.69  fof(f5,axiom,(
% 0.56/0.69    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.56/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.56/0.69  fof(f23,plain,(
% 0.56/0.69    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.56/0.69    inference(cnf_transformation,[],[f13])).
% 0.56/0.69  fof(f13,plain,(
% 0.56/0.69    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.56/0.69    inference(ennf_transformation,[],[f6])).
% 0.56/0.69  fof(f6,axiom,(
% 0.56/0.69    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.56/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.56/0.69  % SZS output end Proof for theBenchmark
% 0.56/0.69  % (7230)------------------------------
% 0.56/0.69  % (7230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.56/0.69  % (7230)Termination reason: Refutation
% 0.56/0.69  
% 0.56/0.69  % (7230)Memory used [KB]: 6140
% 0.56/0.69  % (7230)Time elapsed: 0.116 s
% 0.56/0.69  % (7230)------------------------------
% 0.56/0.69  % (7230)------------------------------
% 0.56/0.69  % (7237)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.56/0.69  % (7089)Success in time 0.328 s
%------------------------------------------------------------------------------
