%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:11 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   50 (  52 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 133 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f30,f84])).

fof(f84,plain,(
    ! [X7] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X7) ),
    inference(resolution,[],[f78,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f78,plain,(
    ! [X0] : v1_xboole_0(k10_relat_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f49,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).

% (16237)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (16249)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (16236)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ) ),
    inference(forward_demodulation,[],[f73,f33])).

fof(f33,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,k1_xboole_0),k2_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k10_relat_1(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f61,f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k10_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f30,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).

fof(f18,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:42:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (16251)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.49  % (16243)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (16243)Refutation not found, incomplete strategy% (16243)------------------------------
% 0.20/0.49  % (16243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16243)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16243)Memory used [KB]: 10490
% 0.20/0.49  % (16243)Time elapsed: 0.058 s
% 0.20/0.49  % (16243)------------------------------
% 0.20/0.49  % (16243)------------------------------
% 0.20/0.50  % (16251)Refutation not found, incomplete strategy% (16251)------------------------------
% 0.20/0.50  % (16251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16251)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16251)Memory used [KB]: 1535
% 0.20/0.50  % (16251)Time elapsed: 0.071 s
% 0.20/0.50  % (16251)------------------------------
% 0.20/0.50  % (16251)------------------------------
% 0.20/0.52  % (16252)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.53  % (16252)Refutation not found, incomplete strategy% (16252)------------------------------
% 0.20/0.53  % (16252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16252)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16252)Memory used [KB]: 1663
% 0.20/0.53  % (16252)Time elapsed: 0.110 s
% 0.20/0.53  % (16252)------------------------------
% 0.20/0.53  % (16252)------------------------------
% 0.20/0.53  % (16238)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.38/0.53  % (16238)Refutation not found, incomplete strategy% (16238)------------------------------
% 1.38/0.53  % (16238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (16244)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.38/0.53  % (16238)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (16238)Memory used [KB]: 10490
% 1.38/0.53  % (16238)Time elapsed: 0.097 s
% 1.38/0.53  % (16238)------------------------------
% 1.38/0.53  % (16238)------------------------------
% 1.38/0.53  % (16235)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.38/0.53  % (16244)Refutation found. Thanks to Tanya!
% 1.38/0.53  % SZS status Theorem for theBenchmark
% 1.38/0.53  % SZS output start Proof for theBenchmark
% 1.38/0.53  fof(f105,plain,(
% 1.38/0.53    $false),
% 1.38/0.53    inference(trivial_inequality_removal,[],[f104])).
% 1.38/0.53  fof(f104,plain,(
% 1.38/0.53    k1_xboole_0 != k1_xboole_0),
% 1.38/0.53    inference(superposition,[],[f30,f84])).
% 1.38/0.53  fof(f84,plain,(
% 1.38/0.53    ( ! [X7] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X7)) )),
% 1.38/0.53    inference(resolution,[],[f78,f47])).
% 1.38/0.53  fof(f47,plain,(
% 1.38/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.38/0.53    inference(resolution,[],[f41,f31])).
% 1.38/0.53  fof(f31,plain,(
% 1.38/0.53    v1_xboole_0(k1_xboole_0)),
% 1.38/0.53    inference(cnf_transformation,[],[f2])).
% 1.38/0.53  fof(f2,axiom,(
% 1.38/0.53    v1_xboole_0(k1_xboole_0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.38/0.53  fof(f41,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f16])).
% 1.38/0.53  fof(f16,plain,(
% 1.38/0.53    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.38/0.53    inference(ennf_transformation,[],[f6])).
% 1.38/0.53  fof(f6,axiom,(
% 1.38/0.53    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.38/0.53  fof(f78,plain,(
% 1.38/0.53    ( ! [X0] : (v1_xboole_0(k10_relat_1(k1_xboole_0,X0))) )),
% 1.38/0.53    inference(resolution,[],[f75,f38])).
% 1.38/0.53  fof(f38,plain,(
% 1.38/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f23])).
% 1.38/0.53  fof(f23,plain,(
% 1.38/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 1.38/0.53  fof(f22,plain,(
% 1.38/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f21,plain,(
% 1.38/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.53    inference(rectify,[],[f20])).
% 1.38/0.53  fof(f20,plain,(
% 1.38/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.53    inference(nnf_transformation,[],[f1])).
% 1.38/0.53  fof(f1,axiom,(
% 1.38/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.38/0.53  fof(f75,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 1.38/0.53    inference(resolution,[],[f74,f50])).
% 1.38/0.53  fof(f50,plain,(
% 1.38/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f49,f35])).
% 1.38/0.53  fof(f35,plain,(
% 1.38/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f4])).
% 1.38/0.53  fof(f4,axiom,(
% 1.38/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.38/0.53  fof(f49,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.38/0.53    inference(resolution,[],[f40,f34])).
% 1.38/0.53  fof(f34,plain,(
% 1.38/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f5])).
% 1.38/0.53  fof(f5,axiom,(
% 1.38/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.38/0.53  fof(f40,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f25])).
% 1.38/0.53  fof(f25,plain,(
% 1.38/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f24])).
% 1.38/0.54  % (16237)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.38/0.54  % (16249)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.38/0.54  % (16236)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f15,plain,(
% 1.38/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,plain,(
% 1.38/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(rectify,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.38/0.54  fof(f74,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 1.38/0.54    inference(forward_demodulation,[],[f73,f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.38/0.54    inference(cnf_transformation,[],[f9])).
% 1.38/0.54  fof(f9,axiom,(
% 1.38/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.38/0.54  fof(f73,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,k1_xboole_0),k2_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k10_relat_1(k1_xboole_0,X1))) )),
% 1.38/0.54    inference(resolution,[],[f61,f31])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | r2_hidden(sK3(X0,X2,X1),k2_relat_1(X1)) | ~r2_hidden(X0,k10_relat_1(X1,X2))) )),
% 1.38/0.54    inference(resolution,[],[f42,f36])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,plain,(
% 1.38/0.54    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.38/0.54    inference(rectify,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.38/0.54    inference(nnf_transformation,[],[f17])).
% 1.38/0.54  fof(f17,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.38/0.54    inference(ennf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f18])).
% 1.38/0.54  fof(f18,plain,(
% 1.38/0.54    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f13,plain,(
% 1.38/0.54    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,negated_conjecture,(
% 1.38/0.54    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.38/0.54    inference(negated_conjecture,[],[f10])).
% 1.38/0.54  fof(f10,conjecture,(
% 1.38/0.54    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (16244)------------------------------
% 1.38/0.54  % (16244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (16244)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (16244)Memory used [KB]: 1663
% 1.38/0.54  % (16244)Time elapsed: 0.095 s
% 1.38/0.54  % (16244)------------------------------
% 1.38/0.54  % (16244)------------------------------
% 1.38/0.54  % (16234)Success in time 0.18 s
%------------------------------------------------------------------------------
