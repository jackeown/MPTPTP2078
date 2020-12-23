%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  58 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 184 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f48,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(forward_demodulation,[],[f46,f38])).

fof(f38,plain,(
    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f26,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,k2_relat_1(sK1))) ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f43,plain,(
    r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f41,plain,(
    r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f40,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f32,f27])).

fof(f27,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (20194)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (20178)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (20178)Refutation not found, incomplete strategy% (20178)------------------------------
% 0.20/0.51  % (20178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20178)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20178)Memory used [KB]: 1663
% 0.20/0.51  % (20178)Time elapsed: 0.111 s
% 0.20/0.51  % (20178)------------------------------
% 0.20/0.51  % (20178)------------------------------
% 0.20/0.51  % (20183)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (20203)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (20188)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (20186)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (20203)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (20194)Refutation not found, incomplete strategy% (20194)------------------------------
% 0.20/0.52  % (20194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20194)Memory used [KB]: 6140
% 0.20/0.52  % (20194)Time elapsed: 0.125 s
% 0.20/0.52  % (20194)------------------------------
% 0.20/0.52  % (20194)------------------------------
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f48,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    k1_xboole_0 = sK0),
% 0.20/0.52    inference(resolution,[],[f47,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f46,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    sK0 = k3_xboole_0(sK0,k2_relat_1(sK1))),
% 0.20/0.52    inference(resolution,[],[f26,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,k2_relat_1(sK1)))) )),
% 0.20/0.52    inference(resolution,[],[f43,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    r1_xboole_0(sK0,k2_relat_1(sK1))),
% 0.20/0.52    inference(resolution,[],[f41,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f40,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.20/0.52    inference(superposition,[],[f32,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (20203)------------------------------
% 0.20/0.52  % (20203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20203)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (20203)Memory used [KB]: 1663
% 0.20/0.52  % (20203)Time elapsed: 0.128 s
% 0.20/0.52  % (20203)------------------------------
% 0.20/0.52  % (20203)------------------------------
% 0.20/0.52  % (20175)Success in time 0.162 s
%------------------------------------------------------------------------------
