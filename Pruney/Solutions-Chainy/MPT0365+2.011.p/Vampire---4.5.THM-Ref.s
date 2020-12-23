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
% DateTime   : Thu Dec  3 12:45:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 171 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  109 ( 646 expanded)
%              Number of equality atoms :   48 ( 174 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f146,f86])).

fof(f86,plain,(
    sK1 != k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f27,f65])).

fof(f65,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18])).

% (8597)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
          & r1_xboole_0(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
        & r1_xboole_0(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

% (8598)Refutation not found, incomplete strategy% (8598)------------------------------
% (8598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

% (8598)Termination reason: Refutation not found, incomplete strategy

% (8598)Memory used [KB]: 10746
% (8598)Time elapsed: 0.107 s
% (8598)------------------------------
% (8598)------------------------------
fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f27,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f146,plain,(
    sK1 = k4_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f142,f145])).

fof(f145,plain,(
    sK1 = k3_subset_1(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f138,f82])).

fof(f82,plain,(
    k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f64,f78])).

fof(f78,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f77,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f77,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f76,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f76,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f75,f39])).

fof(f39,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f75,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f74,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

% (8603)Refutation not found, incomplete strategy% (8603)------------------------------
% (8603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f74,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f67,f65])).

fof(f67,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f60,f64])).

fof(f60,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f64,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f138,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f23])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f142,plain,(
    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f137,f90])).

fof(f90,plain,(
    k3_xboole_0(sK0,sK2) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f89,f29])).

fof(f89,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f88,f32])).

fof(f88,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f87,f24])).

fof(f87,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f31,f65])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

% (8596)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f137,plain,(
    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f33,f88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:53:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (8595)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (8588)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (8611)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (8603)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (8598)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (8606)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (8592)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (8595)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f146,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    sK1 != k4_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(superposition,[],[f27,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(resolution,[],[f32,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    (sK1 != k3_subset_1(sK0,sK2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18])).
% 0.22/0.53  % (8597)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != k3_subset_1(sK0,X2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X2] : (sK1 != k3_subset_1(sK0,X2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != k3_subset_1(sK0,sK2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  % (8598)Refutation not found, incomplete strategy% (8598)------------------------------
% 0.22/0.53  % (8598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f10])).
% 0.22/0.53  fof(f10,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).
% 0.22/0.53  % (8598)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8598)Memory used [KB]: 10746
% 0.22/0.53  % (8598)Time elapsed: 0.107 s
% 0.22/0.53  % (8598)------------------------------
% 0.22/0.53  % (8598)------------------------------
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    sK1 != k3_subset_1(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    sK1 = k4_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f142,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    sK1 = k3_subset_1(sK0,k3_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f138,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f64,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f77,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f76,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f75,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.22/0.53    inference(resolution,[],[f34,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    r1_xboole_0(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f74,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  % (8603)Refutation not found, incomplete strategy% (8603)------------------------------
% 0.22/0.53  % (8603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(backward_demodulation,[],[f67,f65])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2))),
% 0.22/0.53    inference(backward_demodulation,[],[f60,f64])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(k2_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)),k3_subset_1(sK0,sK2))),
% 0.22/0.53    inference(resolution,[],[f30,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f32,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f33,f23])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f137,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK2) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f89,f29])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(resolution,[],[f88,f32])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f87,f24])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(superposition,[],[f31,f65])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % (8596)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k4_xboole_0(sK0,sK2)))),
% 0.22/0.53    inference(resolution,[],[f33,f88])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (8595)------------------------------
% 0.22/0.53  % (8595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8595)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (8595)Memory used [KB]: 6268
% 0.22/0.53  % (8595)Time elapsed: 0.108 s
% 0.22/0.53  % (8595)------------------------------
% 0.22/0.53  % (8595)------------------------------
% 0.22/0.53  % (8587)Success in time 0.161 s
%------------------------------------------------------------------------------
