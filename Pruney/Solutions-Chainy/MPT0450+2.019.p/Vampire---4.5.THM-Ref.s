%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 206 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f67,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f52,f63])).

fof(f63,plain,(
    ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f62,f25])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f61,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f58,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f48,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f38,f30])).

fof(f38,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f55,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f28,f53])).

fof(f53,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (23349)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (23351)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (23349)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f67,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f12])).
% 0.20/0.47  fof(f12,conjecture,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ~v1_relat_1(sK1)),
% 0.20/0.47    inference(resolution,[],[f52,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(subsumption_resolution,[],[f62,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f61,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.20/0.47    inference(superposition,[],[f31,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK0)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(resolution,[],[f58,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | ~v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.48    inference(subsumption_resolution,[],[f57,f26])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f55,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f48,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    inference(rectify,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1))) )),
% 0.20/0.48    inference(superposition,[],[f38,f30])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f28,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.20/0.48    inference(resolution,[],[f39,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X1,X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(resolution,[],[f50,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.20/0.48    inference(resolution,[],[f29,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (23349)------------------------------
% 0.20/0.48  % (23349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23349)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (23349)Memory used [KB]: 1663
% 0.20/0.48  % (23349)Time elapsed: 0.054 s
% 0.20/0.48  % (23349)------------------------------
% 0.20/0.48  % (23349)------------------------------
% 0.20/0.48  % (23347)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (23352)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (23345)Success in time 0.12 s
%------------------------------------------------------------------------------
