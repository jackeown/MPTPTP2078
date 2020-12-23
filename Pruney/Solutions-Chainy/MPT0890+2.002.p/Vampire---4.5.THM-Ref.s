%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 116 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :   78 ( 426 expanded)
%              Number of equality atoms :   68 ( 368 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f36])).

fof(f36,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(subsumption_resolution,[],[f35,f25])).

fof(f25,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    inference(superposition,[],[f15,f24])).

fof(f24,plain,(
    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f23,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != k2_mcart_1(X3)
            | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3))
            | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3)) )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                  & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                  & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f23,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f22,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f21,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f20,f19])).

fof(f19,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f10,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f10,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(definition_unfolding,[],[f18,f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f15,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f35,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
    | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f34])).

fof(f34,plain,
    ( k2_mcart_1(k1_mcart_1(sK3)) != k2_mcart_1(k1_mcart_1(sK3))
    | k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
    | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(backward_demodulation,[],[f9,f31])).

fof(f31,plain,(
    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f15,f26])).

fof(f26,plain,(
    k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)) ),
    inference(superposition,[],[f14,f24])).

fof(f14,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f9,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3)
    | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3))
    | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    inference(superposition,[],[f14,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (6165)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (6165)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f32,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f35,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 0.22/0.55    inference(superposition,[],[f15,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f23,f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    k1_xboole_0 != sK0),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) != k2_mcart_1(X3) | k6_mcart_1(X0,X1,X2,X3) != k2_mcart_1(k1_mcart_1(X3)) | k5_mcart_1(X0,X1,X2,X3) != k1_mcart_1(k1_mcart_1(X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    inference(negated_conjecture,[],[f5])).
% 0.22/0.55  fof(f5,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f22,f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    k1_xboole_0 != sK2),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(subsumption_resolution,[],[f21,f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 0.22/0.55    inference(resolution,[],[f20,f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.22/0.55    inference(definition_unfolding,[],[f10,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f7])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3) )),
% 0.22/0.55    inference(definition_unfolding,[],[f18,f17,f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.42/0.55  fof(f15,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    k2_mcart_1(k1_mcart_1(sK3)) != k2_mcart_1(k1_mcart_1(sK3)) | k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))),
% 1.42/0.55    inference(backward_demodulation,[],[f9,f31])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 1.42/0.55    inference(superposition,[],[f15,f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    k1_mcart_1(sK3) = k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3))),
% 1.42/0.55    inference(superposition,[],[f14,f24])).
% 1.42/0.55  fof(f14,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f4])).
% 1.42/0.55  fof(f9,plain,(
% 1.42/0.55    k7_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(sK3) | k6_mcart_1(sK0,sK1,sK2,sK3) != k2_mcart_1(k1_mcart_1(sK3)) | k5_mcart_1(sK0,sK1,sK2,sK3) != k1_mcart_1(k1_mcart_1(sK3))),
% 1.42/0.55    inference(cnf_transformation,[],[f7])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 1.42/0.55    inference(superposition,[],[f14,f26])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (6165)------------------------------
% 1.42/0.55  % (6165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (6165)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (6165)Memory used [KB]: 6140
% 1.42/0.55  % (6165)Time elapsed: 0.120 s
% 1.42/0.55  % (6165)------------------------------
% 1.42/0.55  % (6165)------------------------------
% 1.42/0.55  % (6158)Success in time 0.191 s
%------------------------------------------------------------------------------
