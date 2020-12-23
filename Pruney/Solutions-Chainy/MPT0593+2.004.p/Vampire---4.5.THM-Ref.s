%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  51 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 143 expanded)
%              Number of equality atoms :   35 (  94 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f12,f24])).

fof(f24,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f23,f14])).

fof(f14,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f23,plain,(
    sK1 = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f22,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f22,plain,(
    sK1 = k3_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f21,f11])).

fof(f11,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k2_relat_1(X1)
                & k1_xboole_0 = k2_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

fof(f21,plain,(
    sK1 = k3_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f9,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f9,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f30,f14])).

fof(f30,plain,(
    sK0 = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f29,f19])).

fof(f29,plain,(
    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f28,f10])).

fof(f10,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f13,f15])).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (17408)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.45  % (17408)Refutation not found, incomplete strategy% (17408)------------------------------
% 0.21/0.45  % (17408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (17408)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (17408)Memory used [KB]: 6012
% 0.21/0.45  % (17408)Time elapsed: 0.032 s
% 0.21/0.45  % (17408)------------------------------
% 0.21/0.45  % (17408)------------------------------
% 0.21/0.48  % (17403)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (17411)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (17411)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f31,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(backward_demodulation,[],[f12,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 = sK1),
% 0.21/0.49    inference(forward_demodulation,[],[f23,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    sK1 = k3_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f22,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    sK1 = k3_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))),
% 0.21/0.49    inference(forward_demodulation,[],[f21,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    sK1 = k3_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.21/0.49    inference(resolution,[],[f9,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    sK0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(forward_demodulation,[],[f30,f14])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    sK0 = k3_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f29,f19])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))),
% 0.21/0.49    inference(forward_demodulation,[],[f28,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.49    inference(resolution,[],[f13,f15])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17411)------------------------------
% 0.21/0.49  % (17411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17411)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17411)Memory used [KB]: 1535
% 0.21/0.49  % (17411)Time elapsed: 0.053 s
% 0.21/0.49  % (17411)------------------------------
% 0.21/0.49  % (17411)------------------------------
% 0.21/0.49  % (17397)Success in time 0.126 s
%------------------------------------------------------------------------------
