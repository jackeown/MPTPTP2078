%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 128 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   20
%              Number of atoms          :  106 ( 363 expanded)
%              Number of equality atoms :   65 ( 204 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f130,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f129,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f129,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f25,f103])).

fof(f103,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f47,f102])).

fof(f102,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f31,f101])).

fof(f101,plain,(
    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f94,f14])).

fof(f14,plain,(
    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f94,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f65,f93])).

fof(f93,plain,(
    k1_mcart_1(sK2) = sK3(sK2) ),
    inference(subsumption_resolution,[],[f92,f15])).

fof(f92,plain,
    ( k1_xboole_0 = sK0
    | k1_mcart_1(sK2) = sK3(sK2) ),
    inference(subsumption_resolution,[],[f91,f16])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_mcart_1(sK2) = sK3(sK2) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_mcart_1(sK2) = sK3(sK2) ),
    inference(superposition,[],[f25,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_mcart_1(sK2) = sK3(sK2) ),
    inference(superposition,[],[f19,f42])).

fof(f42,plain,
    ( sK2 = k4_tarski(sK3(sK2),sK4(sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f37,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f37,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(sK3(sK2),sK4(sK2)) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK3(X0),sK4(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f32,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f24,f13])).

fof(f13,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f19,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f65,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(sK3(sK2),k2_mcart_1(sK2)) ),
    inference(backward_demodulation,[],[f37,f64])).

fof(f64,plain,(
    k2_mcart_1(sK2) = sK4(sK2) ),
    inference(subsumption_resolution,[],[f63,f15])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | k2_mcart_1(sK2) = sK4(sK2) ),
    inference(subsumption_resolution,[],[f62,f16])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k2_mcart_1(sK2) = sK4(sK2) ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k2_mcart_1(sK2) = sK4(sK2) ),
    inference(superposition,[],[f25,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k2_mcart_1(sK2) = sK4(sK2) ),
    inference(superposition,[],[f20,f42])).

fof(f20,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f22,f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(superposition,[],[f18,f42])).

fof(f18,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (2896)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (2896)Refutation not found, incomplete strategy% (2896)------------------------------
% 0.21/0.47  % (2896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2914)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (2896)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2896)Memory used [KB]: 10490
% 0.21/0.48  % (2896)Time elapsed: 0.061 s
% 0.21/0.48  % (2896)------------------------------
% 0.21/0.48  % (2896)------------------------------
% 0.21/0.48  % (2914)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f130,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) != X2 & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.48    inference(superposition,[],[f25,f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f47,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    v1_xboole_0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f31,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    sK2 != k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(backward_demodulation,[],[f65,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    k1_mcart_1(sK2) = sK3(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f15])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | k1_mcart_1(sK2) = sK3(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f16])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_mcart_1(sK2) = sK3(sK2)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_mcart_1(sK2) = sK3(sK2)),
% 0.21/0.48    inference(superposition,[],[f25,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_mcart_1(sK2) = sK3(sK2)),
% 0.21/0.48    inference(superposition,[],[f19,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    sK2 = k4_tarski(sK3(sK2),sK4(sK2)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    inference(resolution,[],[f37,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(sK3(sK2),sK4(sK2))),
% 0.21/0.48    inference(resolution,[],[f32,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK3(X0),sK4(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f24,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(sK3(sK2),k2_mcart_1(sK2))),
% 0.21/0.48    inference(backward_demodulation,[],[f37,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    k2_mcart_1(sK2) = sK4(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f15])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | k2_mcart_1(sK2) = sK4(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f16])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k2_mcart_1(sK2) = sK4(sK2)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k2_mcart_1(sK2) = sK4(sK2)),
% 0.21/0.48    inference(superposition,[],[f25,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k2_mcart_1(sK2) = sK4(sK2)),
% 0.21/0.48    inference(superposition,[],[f20,f42])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f22,f13])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    inference(superposition,[],[f18,f42])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k4_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ~v1_xboole_0(k4_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (2914)------------------------------
% 0.21/0.48  % (2914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2914)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (2914)Memory used [KB]: 1663
% 0.21/0.48  % (2914)Time elapsed: 0.064 s
% 0.21/0.48  % (2914)------------------------------
% 0.21/0.48  % (2914)------------------------------
% 0.21/0.49  % (2888)Success in time 0.124 s
%------------------------------------------------------------------------------
