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
% DateTime   : Thu Dec  3 12:51:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 135 expanded)
%              Number of leaves         :    4 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 356 expanded)
%              Number of equality atoms :   18 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(global_subsumption,[],[f11,f42,f63])).

fof(f63,plain,(
    r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f58,f62])).

fof(f62,plain,(
    sK0 = sK5(sK2,k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f54,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f54,plain,(
    r2_hidden(sK5(sK2,k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(resolution,[],[f38,f42])).

fof(f38,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k11_relat_1(sK2,X2))
      | r2_hidden(sK5(sK2,k1_tarski(X2),X3),k1_tarski(X2)) ) ),
    inference(subsumption_resolution,[],[f36,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f36,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k11_relat_1(sK2,X2))
      | r2_hidden(sK5(sK2,k1_tarski(X2),X3),k1_tarski(X2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f28,f32])).

fof(f32,plain,(
    ! [X4] : k11_relat_1(sK2,X4) = k9_relat_1(sK2,k1_tarski(X4)) ),
    inference(resolution,[],[f12,f13])).

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

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f58,plain,(
    r2_hidden(k4_tarski(sK5(sK2,k1_tarski(sK0),sK1),sK1),sK2) ),
    inference(resolution,[],[f37,f42])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK2,X0))
      | r2_hidden(k4_tarski(sK5(sK2,k1_tarski(X0),X1),X1),sK2) ) ),
    inference(subsumption_resolution,[],[f35,f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(sK2,X0))
      | r2_hidden(k4_tarski(sK5(sK2,k1_tarski(X0),X1),X1),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f29,f32])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f40,f32])).

fof(f40,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0))) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(sK1,k9_relat_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f33,f12])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK0,X0)
      | r2_hidden(sK1,k9_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f10,f27])).

fof(f27,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (23703)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (23698)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (23711)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (23703)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (23717)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (23720)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(global_subsumption,[],[f11,f42,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f58,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    sK0 = sK5(sK2,k1_tarski(sK0),sK1)),
% 0.22/0.52    inference(resolution,[],[f54,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.22/0.52    inference(equality_resolution,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    r2_hidden(sK5(sK2,k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 0.22/0.52    inference(resolution,[],[f38,f42])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k11_relat_1(sK2,X2)) | r2_hidden(sK5(sK2,k1_tarski(X2),X3),k1_tarski(X2))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f36,f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r2_hidden(X1,k11_relat_1(X2,X0))) & v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k11_relat_1(sK2,X2)) | r2_hidden(sK5(sK2,k1_tarski(X2),X3),k1_tarski(X2)) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(superposition,[],[f28,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X4] : (k11_relat_1(sK2,X4) = k9_relat_1(sK2,k1_tarski(X4))) )),
% 0.22/0.52    inference(resolution,[],[f12,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | r2_hidden(sK5(X0,X1,X3),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK5(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK5(sK2,k1_tarski(sK0),sK1),sK1),sK2)),
% 0.22/0.52    inference(resolution,[],[f37,f42])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK2,X0)) | r2_hidden(k4_tarski(sK5(sK2,k1_tarski(X0),X1),X1),sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f35,f12])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK2,X0)) | r2_hidden(k4_tarski(sK5(sK2,k1_tarski(X0),X1),X1),sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.52    inference(superposition,[],[f29,f32])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK5(X0,X1,X3),X3),X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.52    inference(forward_demodulation,[],[f40,f32])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0)))),
% 0.22/0.52    inference(resolution,[],[f34,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.22/0.52    inference(equality_resolution,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.22/0.52    inference(equality_resolution,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(sK1,k11_relat_1(sK2,sK0)) | r2_hidden(sK1,k9_relat_1(sK2,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f33,f12])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK1,k11_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,X0) | r2_hidden(sK1,k9_relat_1(sK2,X0))) )),
% 0.22/0.52    inference(resolution,[],[f10,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X4,X3),X0) | ~v1_relat_1(X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK0,sK1),sK2) | r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k11_relat_1(sK2,sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23703)------------------------------
% 0.22/0.52  % (23703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23703)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23703)Memory used [KB]: 6140
% 0.22/0.52  % (23703)Time elapsed: 0.092 s
% 0.22/0.52  % (23703)------------------------------
% 0.22/0.52  % (23703)------------------------------
% 0.22/0.52  % (23715)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (23697)Success in time 0.158 s
%------------------------------------------------------------------------------
