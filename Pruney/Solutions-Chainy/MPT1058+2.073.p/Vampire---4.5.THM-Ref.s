%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  60 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 152 expanded)
%              Number of equality atoms :   35 (  61 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f141,f33])).

fof(f33,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f141,plain,(
    ~ r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2)
    | ~ r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(superposition,[],[f83,f108])).

fof(f108,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f107,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f107,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X2)),X3) ) ),
    inference(subsumption_resolution,[],[f102,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f102,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X2)),X3) ) ),
    inference(superposition,[],[f79,f63])).

fof(f63,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f62,f36])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f79,plain,(
    ! [X4,X2,X3] :
      ( k10_relat_1(X2,X4) = k3_xboole_0(X3,k10_relat_1(X2,X4))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X3] :
      ( k10_relat_1(X2,X4) = k3_xboole_0(X3,k10_relat_1(X2,X4))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f83,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f78,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f34,f46])).

fof(f34,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (2900)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (2907)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (2897)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (2904)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (2897)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f141,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f30,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.21/0.45    inference(pure_predicate_removal,[],[f17])).
% 0.21/0.45  fof(f17,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.21/0.45    inference(negated_conjecture,[],[f16])).
% 0.21/0.45  fof(f16,conjecture,(
% 0.21/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    ~r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f139])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) | ~r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.21/0.45    inference(superposition,[],[f83,f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f107,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(k1_relat_1(k6_relat_1(X2)),X3)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f102,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~v1_relat_1(k6_relat_1(X2)) | ~r1_tarski(k1_relat_1(k6_relat_1(X2)),X3)) )),
% 0.21/0.45    inference(superposition,[],[f79,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 0.21/0.45    inference(forward_demodulation,[],[f62,f36])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f61,f35])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.45    inference(superposition,[],[f39,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ( ! [X4,X2,X3] : (k10_relat_1(X2,X4) = k3_xboole_0(X3,k10_relat_1(X2,X4)) | ~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X3)) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X4,X2,X3] : (k10_relat_1(X2,X4) = k3_xboole_0(X3,k10_relat_1(X2,X4)) | ~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 0.21/0.45    inference(superposition,[],[f46,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 0.21/0.45    inference(subsumption_resolution,[],[f78,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0)),
% 0.21/0.45    inference(superposition,[],[f34,f46])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (2897)------------------------------
% 0.21/0.45  % (2897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (2897)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (2897)Memory used [KB]: 1663
% 0.21/0.45  % (2897)Time elapsed: 0.049 s
% 0.21/0.45  % (2897)------------------------------
% 0.21/0.45  % (2897)------------------------------
% 0.21/0.45  % (2893)Success in time 0.095 s
%------------------------------------------------------------------------------
