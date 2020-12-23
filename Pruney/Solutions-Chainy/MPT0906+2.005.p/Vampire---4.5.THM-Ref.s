%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 156 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 314 expanded)
%              Number of equality atoms :   81 ( 265 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10536)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (10539)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% (10542)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (10539)Refutation not found, incomplete strategy% (10539)------------------------------
% (10539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10539)Termination reason: Refutation not found, incomplete strategy

% (10539)Memory used [KB]: 10618
% (10539)Time elapsed: 0.061 s
% (10539)------------------------------
% (10539)------------------------------
fof(f74,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f37,f35])).

fof(f35,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f34,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f34,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f33,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f26,f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f37,plain,(
    ! [X4,X3] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4) ),
    inference(superposition,[],[f30,f35])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f72,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f18,f71])).

fof(f71,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f46,f39])).

fof(f46,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f45,f35])).

fof(f45,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f31,f30])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f18,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f66,f61])).

fof(f61,plain,
    ( sK2 != k1_mcart_1(sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1) )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_mcart_1(X2) != X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK2 = k1_mcart_1(sK2) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK2 = k1_mcart_1(sK2) ),
    inference(superposition,[],[f63,f20])).

fof(f20,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( sK2 != k2_mcart_1(sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f28,f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k2_mcart_1(X2) != X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (10538)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (10537)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (10544)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (10531)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (10530)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (10531)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  % (10536)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (10539)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (10542)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (10539)Refutation not found, incomplete strategy% (10539)------------------------------
% 0.22/0.49  % (10539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10539)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (10539)Memory used [KB]: 10618
% 0.22/0.49  % (10539)Time elapsed: 0.061 s
% 0.22/0.49  % (10539)------------------------------
% 0.22/0.49  % (10539)------------------------------
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f72,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X4)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f37,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f34,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f33,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.22/0.49    inference(superposition,[],[f26,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k5_xboole_0(X1,X1)) )),
% 0.22/0.49    inference(superposition,[],[f26,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(X3,X3),X4)) )),
% 0.22/0.49    inference(superposition,[],[f30,f35])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.22/0.49    inference(backward_demodulation,[],[f18,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    k1_xboole_0 = sK0),
% 0.22/0.49    inference(subsumption_resolution,[],[f69,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f46,f39])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f45,f35])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f41,f35])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X0),X1) = k2_zfmisc_1(X0,k4_xboole_0(X1,X1))) )),
% 0.22/0.49    inference(superposition,[],[f31,f30])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.22/0.49    inference(superposition,[],[f18,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    sK2 != k1_mcart_1(sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.49    inference(resolution,[],[f27,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) => (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_mcart_1(X2) != X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK2 = k1_mcart_1(sK2)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    sK2 != sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK2 = k1_mcart_1(sK2)),
% 0.22/0.49    inference(superposition,[],[f63,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    sK2 != k2_mcart_1(sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.49    inference(resolution,[],[f28,f19])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k2_mcart_1(X2) != X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10531)------------------------------
% 0.22/0.49  % (10531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10531)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10531)Memory used [KB]: 1663
% 0.22/0.49  % (10531)Time elapsed: 0.063 s
% 0.22/0.49  % (10531)------------------------------
% 0.22/0.49  % (10531)------------------------------
% 0.22/0.49  % (10527)Success in time 0.128 s
%------------------------------------------------------------------------------
