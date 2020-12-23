%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  63 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 157 expanded)
%              Number of equality atoms :   39 ( 106 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f13,f31])).

fof(f31,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f30,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f30,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f29,f24])).

fof(f24,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f29,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f27,f12])).

fof(f12,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_xboole_0 = k1_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).

fof(f27,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    inference(resolution,[],[f22,f10])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f16,f17])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f13,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f36,f21])).

fof(f36,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f35,f24])).

fof(f35,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0)))) ),
    inference(forward_demodulation,[],[f28,f11])).

fof(f11,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(resolution,[],[f22,f14])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (8873)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.48  % (8873)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f37,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(backward_demodulation,[],[f13,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    k1_xboole_0 = sK1),
% 0.21/0.48    inference(forward_demodulation,[],[f30,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f15,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))),
% 0.21/0.48    inference(forward_demodulation,[],[f29,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK1))))),
% 0.21/0.48    inference(forward_demodulation,[],[f27,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_relat_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))),
% 0.21/0.48    inference(resolution,[],[f22,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f16,f17])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    sK0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(forward_demodulation,[],[f36,f21])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))),
% 0.21/0.48    inference(forward_demodulation,[],[f35,f24])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK0))))),
% 0.21/0.48    inference(forward_demodulation,[],[f28,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.48    inference(resolution,[],[f22,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (8873)------------------------------
% 0.21/0.48  % (8873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8873)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (8873)Memory used [KB]: 6140
% 0.21/0.48  % (8873)Time elapsed: 0.061 s
% 0.21/0.48  % (8873)------------------------------
% 0.21/0.48  % (8873)------------------------------
% 0.21/0.48  % (8866)Success in time 0.114 s
%------------------------------------------------------------------------------
