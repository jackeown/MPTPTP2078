%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  89 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 286 expanded)
%              Number of equality atoms :   62 ( 110 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f133,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f25,f130])).

fof(f130,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f129,f24])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f129,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( sK1 != sK1
    | sK0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f120,f73])).

fof(f73,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f70,f69])).

fof(f69,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f21,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f21,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f57,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f57,plain,(
    m1_subset_1(sK2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f21,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f120,plain,(
    ! [X5] :
      ( sK1 != k1_tarski(X5)
      | sK0 = k1_tarski(X5)
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f118,f54])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f44,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f49,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f118,plain,(
    ! [X5] :
      ( k1_tarski(X5) != k5_xboole_0(sK1,k1_xboole_0)
      | sK0 = k1_tarski(X5)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f81,f51])).

fof(f51,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    ! [X4,X5,X3] :
      ( k1_tarski(X3) != k5_xboole_0(X5,k4_xboole_0(X4,X5))
      | k1_tarski(X3) = X4
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k1_tarski(X0) = X2
      | k1_tarski(X0) != k5_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_tarski(X0) = X2
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:31:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (4343)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.47  % (4343)Refutation not found, incomplete strategy% (4343)------------------------------
% 0.21/0.47  % (4343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4351)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.48  % (4343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4343)Memory used [KB]: 6268
% 0.21/0.48  % (4343)Time elapsed: 0.050 s
% 0.21/0.48  % (4343)------------------------------
% 0.21/0.48  % (4343)------------------------------
% 0.21/0.49  % (4351)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f25,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    sK0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    sK0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    sK1 != sK1 | sK0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(superposition,[],[f120,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f70,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f22,f21,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f21,f57,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    m1_subset_1(sK2(sK1),sK1)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f22,f21,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X5] : (sK1 != k1_tarski(X5) | sK0 = k1_tarski(X5) | k1_xboole_0 = sK0) )),
% 0.21/0.49    inference(forward_demodulation,[],[f118,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(backward_demodulation,[],[f44,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f49,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f26,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.49    inference(rectify,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X5] : (k1_tarski(X5) != k5_xboole_0(sK1,k1_xboole_0) | sK0 = k1_tarski(X5) | k1_xboole_0 = sK0) )),
% 0.21/0.49    inference(superposition,[],[f81,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f23,f27])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k1_tarski(X3) != k5_xboole_0(X5,k4_xboole_0(X4,X5)) | k1_tarski(X3) = X4 | k1_xboole_0 = X4) )),
% 0.21/0.49    inference(resolution,[],[f47,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP3(X2,X1,X0) | k1_xboole_0 = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | k1_tarski(X0) = X2 | k1_tarski(X0) != k5_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f40,f43])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_tarski(X0) = X2 | sP3(X2,X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4351)------------------------------
% 0.21/0.49  % (4351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4351)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4351)Memory used [KB]: 1791
% 0.21/0.49  % (4351)Time elapsed: 0.063 s
% 0.21/0.49  % (4351)------------------------------
% 0.21/0.49  % (4351)------------------------------
% 0.21/0.49  % (4330)Success in time 0.129 s
%------------------------------------------------------------------------------
