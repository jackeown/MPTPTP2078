%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 123 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :   20
%              Number of atoms          :  103 ( 355 expanded)
%              Number of equality atoms :   48 ( 150 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f105,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f102,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f102,plain,(
    ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f83,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f83,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f80,f67])).

fof(f67,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f64,f22])).

fof(f64,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f58,f23])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f34,f25])).

fof(f34,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f32,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f30,f31])).

fof(f31,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f18,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK1 != k1_subset_1(sK0)
      | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & ( sK1 = k1_subset_1(sK0)
      | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k1_subset_1(sK0)
        | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & ( sK1 = k1_subset_1(sK0)
        | r1_tarski(sK1,k3_subset_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f30,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f19,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f19,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f38,f67])).

fof(f38,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f33,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f29,f31])).

fof(f29,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f20,f21])).

fof(f20,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:56:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (21175)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.44  % (21167)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.45  % (21175)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % (21167)Refutation not found, incomplete strategy% (21167)------------------------------
% 0.20/0.45  % (21167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (21167)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (21167)Memory used [KB]: 6140
% 0.20/0.45  % (21167)Time elapsed: 0.004 s
% 0.20/0.45  % (21167)------------------------------
% 0.20/0.45  % (21167)------------------------------
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f105,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    ~r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.45    inference(resolution,[],[f102,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    ~r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f101])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.20/0.45    inference(superposition,[],[f83,f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.20/0.45    inference(forward_demodulation,[],[f80,f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    k1_xboole_0 = sK1),
% 0.20/0.45    inference(subsumption_resolution,[],[f64,f22])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    k1_xboole_0 = sK1 | ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.20/0.45    inference(resolution,[],[f58,f23])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(superposition,[],[f34,f25])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.20/0.45    inference(resolution,[],[f32,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.45    inference(nnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.20/0.45    inference(backward_demodulation,[],[f30,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(resolution,[],[f18,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    (sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))) & (sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(flattening,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.45    inference(forward_demodulation,[],[f19,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f71])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(backward_demodulation,[],[f38,f67])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    k1_xboole_0 != sK1 | k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(resolution,[],[f33,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ~r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 != sK1),
% 0.20/0.45    inference(backward_demodulation,[],[f29,f31])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.45    inference(forward_demodulation,[],[f20,f21])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (21175)------------------------------
% 0.20/0.45  % (21175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (21175)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (21175)Memory used [KB]: 1663
% 0.20/0.45  % (21175)Time elapsed: 0.037 s
% 0.20/0.45  % (21175)------------------------------
% 0.20/0.45  % (21175)------------------------------
% 0.20/0.45  % (21149)Success in time 0.104 s
%------------------------------------------------------------------------------
