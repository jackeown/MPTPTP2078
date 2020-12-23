%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 101 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f40])).

fof(f40,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f39,f35])).

fof(f35,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f22,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f39,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f38,f36])).

fof(f36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f21,f20])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(resolution,[],[f18,f32])).

fof(f32,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(f18,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f64,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[],[f30,f60])).

fof(f60,plain,(
    k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(f57,plain,
    ( ~ v1_relat_1(sK1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(superposition,[],[f25,f47])).

fof(f47,plain,(
    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f45,f27])).

fof(f45,plain,
    ( ~ v1_relat_1(sK1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0] : v5_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2] :
      ( ~ v5_relat_1(X2,k1_xboole_0)
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = k2_relat_1(X2) ) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f30,plain,(
    ! [X0] : v5_ordinal1(sK1(X0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (4568)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.45  % (4570)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.45  % (4578)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.45  % (4578)Refutation not found, incomplete strategy% (4578)------------------------------
% 0.21/0.45  % (4578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (4578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (4578)Memory used [KB]: 10618
% 0.21/0.45  % (4578)Time elapsed: 0.041 s
% 0.21/0.45  % (4578)------------------------------
% 0.21/0.45  % (4578)------------------------------
% 0.21/0.46  % (4562)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (4576)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.46  % (4576)Refutation not found, incomplete strategy% (4576)------------------------------
% 0.21/0.46  % (4576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4562)Refutation not found, incomplete strategy% (4562)------------------------------
% 0.21/0.46  % (4562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4562)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (4562)Memory used [KB]: 6012
% 0.21/0.46  % (4562)Time elapsed: 0.046 s
% 0.21/0.46  % (4562)------------------------------
% 0.21/0.46  % (4562)------------------------------
% 0.21/0.46  % (4568)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f64,f40])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f39,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    v1_funct_1(k1_xboole_0)),
% 0.21/0.46    inference(superposition,[],[f22,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f38,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v1_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(superposition,[],[f21,f20])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.46    inference(resolution,[],[f18,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.46    inference(negated_conjecture,[],[f10])).
% 0.21/0.46  fof(f10,conjecture,(
% 0.21/0.46    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    v5_ordinal1(k1_xboole_0)),
% 0.21/0.46    inference(superposition,[],[f30,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    k1_xboole_0 = sK1(k1_xboole_0)),
% 0.21/0.46    inference(subsumption_resolution,[],[f57,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : ? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ~v1_relat_1(sK1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0)),
% 0.21/0.46    inference(superposition,[],[f25,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))),
% 0.21/0.46    inference(subsumption_resolution,[],[f45,f27])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ~v1_relat_1(sK1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(sK1(k1_xboole_0))),
% 0.21/0.46    inference(resolution,[],[f42,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0] : (v5_relat_1(sK1(X0),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2] : (~v5_relat_1(X2,k1_xboole_0) | ~v1_relat_1(X2) | k1_xboole_0 = k2_relat_1(X2)) )),
% 0.21/0.46    inference(resolution,[],[f34,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (v5_ordinal1(sK1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (4568)------------------------------
% 0.21/0.46  % (4568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4568)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (4568)Memory used [KB]: 6140
% 0.21/0.46  % (4568)Time elapsed: 0.061 s
% 0.21/0.46  % (4568)------------------------------
% 0.21/0.46  % (4568)------------------------------
% 0.21/0.46  % (4576)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  % (4552)Success in time 0.11 s
%------------------------------------------------------------------------------
