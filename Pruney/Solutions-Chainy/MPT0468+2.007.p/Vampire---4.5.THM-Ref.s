%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  72 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :   90 ( 183 expanded)
%              Number of equality atoms :   20 (  54 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f22])).

fof(f22,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f18,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != sK0
    & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != sK0
      & ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f96,plain,(
    sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f94,f31])).

fof(f31,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f94,plain,
    ( ~ sQ4_eqProxy(sK0,sK0)
    | sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(resolution,[],[f89,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f20,f21])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK0)
      | ~ sQ4_eqProxy(X0,sK0) ) ),
    inference(resolution,[],[f67,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(sK3(X0),X1)
      | ~ sQ4_eqProxy(X0,sK0) ) ),
    inference(resolution,[],[f59,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k4_tarski(sK1(X1),sK2(X1)),X1)
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f19,f21])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK1(X1),sK2(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK1(X1),sK2(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f12])).

fof(f12,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK1(X1),sK2(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f59,plain,(
    ! [X6,X4,X5] :
      ( ~ sQ4_eqProxy(k4_tarski(X5,X6),sK3(X4))
      | ~ sQ4_eqProxy(X4,sK0) ) ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ4_eqProxy(sK3(X0),k4_tarski(X1,X2))
      | ~ sQ4_eqProxy(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ sQ4_eqProxy(k1_xboole_0,X0)
      | ~ sQ4_eqProxy(X0,sK0) ) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(X0,X2)
      | ~ sQ4_eqProxy(X1,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ4_eqProxy(X0,sK0)
      | ~ sQ4_eqProxy(sK3(X0),k4_tarski(X1,X2))
      | sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ sQ4_eqProxy(X0,sK0)
      | ~ sQ4_eqProxy(X1,k4_tarski(X2,X3)) ) ),
    inference(resolution,[],[f29,f17])).

fof(f17,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ r2_hidden(X0,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:13:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (32468)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (32468)Refutation not found, incomplete strategy% (32468)------------------------------
% 0.21/0.47  % (32468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32468)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (32468)Memory used [KB]: 6012
% 0.21/0.47  % (32468)Time elapsed: 0.060 s
% 0.21/0.47  % (32468)------------------------------
% 0.21/0.47  % (32468)------------------------------
% 0.21/0.48  % (32476)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (32476)Refutation not found, incomplete strategy% (32476)------------------------------
% 0.21/0.48  % (32476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (32476)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (32476)Memory used [KB]: 10490
% 0.21/0.48  % (32476)Time elapsed: 0.060 s
% 0.21/0.48  % (32476)------------------------------
% 0.21/0.48  % (32476)------------------------------
% 0.21/0.49  % (32461)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (32461)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f18,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),sK0) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) & v1_relat_1(X0)) => (k1_xboole_0 != sK0 & ! [X2,X1] : ~r2_hidden(k4_tarski(X1,X2),sK0) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : ((k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f21])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~sQ4_eqProxy(sK0,sK0) | sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.49    inference(resolution,[],[f89,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f20,f21])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK3(X0),sK0) | ~sQ4_eqProxy(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f67,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(sK3(X0),X1) | ~sQ4_eqProxy(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f59,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sQ4_eqProxy(k4_tarski(sK1(X1),sK2(X1)),X1) | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f19,f21])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_tarski(sK1(X1),sK2(X1)) = X1 | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k4_tarski(sK1(X1),sK2(X1)) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 => k4_tarski(sK1(X1),sK2(X1)) = X1)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X6,X4,X5] : (~sQ4_eqProxy(k4_tarski(X5,X6),sK3(X4)) | ~sQ4_eqProxy(X4,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f57,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f21])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sQ4_eqProxy(sK3(X0),k4_tarski(X1,X2)) | ~sQ4_eqProxy(X0,sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f55,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (~sQ4_eqProxy(k1_xboole_0,X0) | ~sQ4_eqProxy(X0,sK0)) )),
% 0.21/0.49    inference(resolution,[],[f33,f22])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sQ4_eqProxy(X0,X2) | ~sQ4_eqProxy(X1,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f21])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sQ4_eqProxy(X0,sK0) | ~sQ4_eqProxy(sK3(X0),k4_tarski(X1,X2)) | sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f38,f24])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,X0) | ~sQ4_eqProxy(X0,sK0) | ~sQ4_eqProxy(X1,k4_tarski(X2,X3))) )),
% 0.21/0.49    inference(resolution,[],[f29,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~sQ4_eqProxy(X2,X3) | ~r2_hidden(X0,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f21])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (32461)------------------------------
% 0.21/0.49  % (32461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32461)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (32461)Memory used [KB]: 6140
% 0.21/0.49  % (32461)Time elapsed: 0.003 s
% 0.21/0.49  % (32461)------------------------------
% 0.21/0.49  % (32461)------------------------------
% 0.21/0.49  % (32455)Success in time 0.127 s
%------------------------------------------------------------------------------
