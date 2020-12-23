%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 142 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 444 expanded)
%              Number of equality atoms :   64 ( 213 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f89])).

fof(f89,plain,(
    k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f86,plain,(
    ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f33,f85])).

fof(f85,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f83,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( k7_relat_1(sK1,sK0) = k3_xboole_0(k7_relat_1(sK1,sK0),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f79,f50])).

fof(f50,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f79,plain,
    ( k7_relat_1(sK1,sK0) = k3_xboole_0(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0))))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f78,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f32,f44])).

fof(f32,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f78,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(k7_relat_1(sK1,X0),k2_zfmisc_1(k3_xboole_0(k1_relat_1(sK1),X0),k2_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(forward_demodulation,[],[f76,f67])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f76,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0)))) ),
    inference(resolution,[],[f61,f31])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1)))) ) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f33,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f92,f34])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f92,plain,(
    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f67,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (31122)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.48  % (31122)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (31115)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.50    inference(resolution,[],[f86,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f33,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f83,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(resolution,[],[f44,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    k7_relat_1(sK1,sK0) = k3_xboole_0(k7_relat_1(sK1,sK0),k1_xboole_0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f79,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    k7_relat_1(sK1,sK0) = k3_xboole_0(k7_relat_1(sK1,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK1,sK0)))) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.50    inference(superposition,[],[f78,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f32,f44])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X0] : (k7_relat_1(sK1,X0) = k3_xboole_0(k7_relat_1(sK1,X0),k2_zfmisc_1(k3_xboole_0(k1_relat_1(sK1),X0),k2_relat_1(k7_relat_1(sK1,X0))))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f76,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.20/0.50    inference(resolution,[],[f43,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0] : (k7_relat_1(sK1,X0) = k3_xboole_0(k7_relat_1(sK1,X0),k2_zfmisc_1(k1_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(k7_relat_1(sK1,X0))))) )),
% 0.20/0.50    inference(resolution,[],[f61,f31])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k7_relat_1(X0,X1)),k2_relat_1(k7_relat_1(X0,X1))))) )),
% 0.20/0.50    inference(resolution,[],[f37,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f92,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.50    inference(superposition,[],[f67,f85])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (31122)------------------------------
% 0.20/0.50  % (31122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (31122)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (31122)Memory used [KB]: 6268
% 0.20/0.50  % (31122)Time elapsed: 0.060 s
% 0.20/0.50  % (31122)------------------------------
% 0.20/0.50  % (31122)------------------------------
% 0.20/0.50  % (31114)Success in time 0.142 s
%------------------------------------------------------------------------------
