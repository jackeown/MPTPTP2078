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
% DateTime   : Thu Dec  3 12:54:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   18
%              Number of atoms          :  100 ( 145 expanded)
%              Number of equality atoms :   36 (  49 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23810)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f148,f34])).

fof(f34,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f33,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f148,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,sK0) ),
    inference(superposition,[],[f22,f119])).

fof(f119,plain,(
    ! [X2,X3] :
      ( k9_relat_1(k6_relat_1(X2),X3) = X3
      | ~ r1_tarski(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k9_relat_1(k6_relat_1(X2),X3) = X3
      | ~ r1_tarski(X3,X2) ) ),
    inference(forward_demodulation,[],[f117,f26])).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f117,plain,(
    ! [X2,X3] :
      ( k9_relat_1(k6_relat_1(X2),X3) = X3
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X3,k2_relat_1(k6_relat_1(X2))) ) ),
    inference(subsumption_resolution,[],[f116,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f116,plain,(
    ! [X2,X3] :
      ( k9_relat_1(k6_relat_1(X2),X3) = X3
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X3,k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f112,f24])).

fof(f24,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f112,plain,(
    ! [X2,X3] :
      ( k9_relat_1(k6_relat_1(X2),X3) = X3
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X3,k2_relat_1(k6_relat_1(X2)))
      | ~ v1_funct_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f45,f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

% (23820)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f45,plain,(
    ! [X6,X4,X5] :
      ( k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5)
      | ~ r1_tarski(X5,X4) ) ),
    inference(forward_demodulation,[],[f44,f26])).

fof(f44,plain,(
    ! [X6,X4,X5] :
      ( k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5)
      | ~ r1_tarski(X5,k2_relat_1(k6_relat_1(X4))) ) ),
    inference(subsumption_resolution,[],[f43,f23])).

fof(f43,plain,(
    ! [X6,X4,X5] :
      ( k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5)
      | ~ r1_tarski(X5,k2_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X6,X4,X5] :
      ( k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5)
      | ~ r1_tarski(X5,k2_relat_1(k6_relat_1(X4)))
      | ~ v1_funct_1(k6_relat_1(X4))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f37,f32])).

fof(f37,plain,(
    ! [X2,X0,X1] : k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2) ),
    inference(subsumption_resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f35,f23])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f22,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (23808)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (23807)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (23811)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (23818)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (23808)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (23819)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  % (23810)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0)),
% 0.21/0.48    inference(resolution,[],[f33,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    sK1 != sK1 | ~r1_tarski(sK1,sK0)),
% 0.21/0.48    inference(superposition,[],[f22,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = X3 | ~r1_tarski(X3,X2)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k9_relat_1(k6_relat_1(X2),X3) = X3 | ~r1_tarski(X3,X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f117,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = X3 | ~r1_tarski(X3,X2) | ~r1_tarski(X3,k2_relat_1(k6_relat_1(X2)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = X3 | ~r1_tarski(X3,X2) | ~r1_tarski(X3,k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(X2),X3) = X3 | ~r1_tarski(X3,X2) | ~r1_tarski(X3,k2_relat_1(k6_relat_1(X2))) | ~v1_funct_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.21/0.48    inference(superposition,[],[f70,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.48    inference(superposition,[],[f45,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % (23820)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.48    inference(rectify,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5) | ~r1_tarski(X5,X4)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f44,f26])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5) | ~r1_tarski(X5,k2_relat_1(k6_relat_1(X4)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f43,f23])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5) | ~r1_tarski(X5,k2_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k6_relat_1(X4))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f41,f24])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (k9_relat_1(k6_relat_1(k3_xboole_0(X6,X4)),k10_relat_1(k6_relat_1(X4),X5)) = k9_relat_1(k6_relat_1(X6),X5) | ~r1_tarski(X5,k2_relat_1(k6_relat_1(X4))) | ~v1_funct_1(k6_relat_1(X4)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 0.21/0.48    inference(superposition,[],[f37,f32])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f36,f23])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f35,f23])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X0),X2)) = k9_relat_1(k6_relat_1(k3_xboole_0(X1,X0)),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(superposition,[],[f31,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (23808)------------------------------
% 0.21/0.48  % (23808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23808)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (23808)Memory used [KB]: 1791
% 0.21/0.48  % (23808)Time elapsed: 0.057 s
% 0.21/0.48  % (23808)------------------------------
% 0.21/0.48  % (23808)------------------------------
% 0.21/0.48  % (23821)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (23822)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (23804)Success in time 0.12 s
%------------------------------------------------------------------------------
