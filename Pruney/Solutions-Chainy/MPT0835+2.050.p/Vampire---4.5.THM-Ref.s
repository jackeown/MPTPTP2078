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
% DateTime   : Thu Dec  3 12:57:22 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 220 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 ( 477 expanded)
%              Number of equality atoms :   65 ( 233 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f99,f74])).

fof(f74,plain,(
    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f55,f72])).

fof(f72,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f68,f65])).

fof(f65,plain,(
    ! [X1] : k8_relset_1(sK1,k2_relat_1(sK2),sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f59,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f58,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0)))) ) ),
    inference(resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f68,plain,(
    k1_relat_1(sK2) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f63,f60])).

fof(f60,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f59,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f63,plain,(
    k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,k2_relat_1(sK2)) ),
    inference(resolution,[],[f59,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f55,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f50,f53])).

fof(f53,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    inference(superposition,[],[f52,f44])).

fof(f44,plain,(
    ! [X0] : k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f31,f22])).

fof(f52,plain,(
    k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f51,f37])).

fof(f37,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f26,f22])).

fof(f51,plain,(
    k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2) ),
    inference(resolution,[],[f29,f22])).

fof(f50,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f49,f44])).

fof(f49,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(backward_demodulation,[],[f45,f48])).

fof(f48,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f47,f39])).

fof(f39,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f47,plain,(
    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f46,f41])).

fof(f41,plain,(
    ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f46,plain,(
    k2_relset_1(sK1,sK0,sK2) = k7_relset_1(sK1,sK0,sK2,sK1) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f43,f44])).

fof(f43,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | k2_relat_1(sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) ),
    inference(forward_demodulation,[],[f42,f41])).

fof(f42,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f40,f41])).

fof(f40,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f38,f39])).

fof(f38,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) ),
    inference(backward_demodulation,[],[f21,f37])).

fof(f21,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(superposition,[],[f85,f81])).

fof(f81,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),sK0,sK2,X0) ),
    inference(resolution,[],[f75,f30])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0))) ),
    inference(resolution,[],[f69,f22])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2))) ) ),
    inference(resolution,[],[f33,f34])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f85,plain,(
    k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f79,f78])).

fof(f78,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK0,sK2) ),
    inference(resolution,[],[f75,f27])).

fof(f79,plain,(
    k2_relset_1(k1_relat_1(sK2),sK0,sK2) = k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f75,f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_vampire %s %d
% 0.16/0.37  % Computer   : n008.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % WCLimit    : 600
% 0.16/0.37  % DateTime   : Tue Dec  1 11:23:15 EST 2020
% 0.23/0.37  % CPUTime    : 
% 0.24/0.47  % (32637)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.24/0.47  % (32627)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.24/0.49  % (32637)Refutation found. Thanks to Tanya!
% 0.24/0.49  % SZS status Theorem for theBenchmark
% 0.24/0.49  % SZS output start Proof for theBenchmark
% 0.24/0.49  fof(f101,plain,(
% 0.24/0.49    $false),
% 0.24/0.49    inference(subsumption_resolution,[],[f99,f74])).
% 0.24/0.49  fof(f74,plain,(
% 0.24/0.49    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.24/0.49    inference(subsumption_resolution,[],[f55,f72])).
% 0.24/0.49  fof(f72,plain,(
% 0.24/0.49    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.24/0.49    inference(superposition,[],[f68,f65])).
% 0.24/0.49  fof(f65,plain,(
% 0.24/0.49    ( ! [X1] : (k8_relset_1(sK1,k2_relat_1(sK2),sK2,X1) = k10_relat_1(sK2,X1)) )),
% 0.24/0.49    inference(resolution,[],[f59,f31])).
% 0.24/0.49  fof(f31,plain,(
% 0.24/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f16])).
% 0.24/0.49  fof(f16,plain,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.49    inference(ennf_transformation,[],[f5])).
% 0.24/0.49  fof(f5,axiom,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.24/0.49  fof(f59,plain,(
% 0.24/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK2))))),
% 0.24/0.49    inference(resolution,[],[f58,f22])).
% 0.24/0.49  fof(f22,plain,(
% 0.24/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.24/0.49    inference(cnf_transformation,[],[f11])).
% 0.24/0.49  fof(f11,plain,(
% 0.24/0.49    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.24/0.49    inference(ennf_transformation,[],[f10])).
% 0.24/0.49  fof(f10,negated_conjecture,(
% 0.24/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.24/0.49    inference(negated_conjecture,[],[f9])).
% 0.24/0.49  fof(f9,conjecture,(
% 0.24/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 0.24/0.49  fof(f58,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(X0))))) )),
% 0.24/0.49    inference(resolution,[],[f32,f34])).
% 0.24/0.49  fof(f34,plain,(
% 0.24/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.24/0.49    inference(equality_resolution,[],[f24])).
% 0.24/0.49  fof(f24,plain,(
% 0.24/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.24/0.49    inference(cnf_transformation,[],[f1])).
% 0.24/0.49  fof(f1,axiom,(
% 0.24/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.24/0.49  fof(f32,plain,(
% 0.24/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.24/0.49    inference(cnf_transformation,[],[f18])).
% 0.24/0.49  fof(f18,plain,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.24/0.49    inference(flattening,[],[f17])).
% 0.24/0.49  fof(f17,plain,(
% 0.24/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.24/0.49    inference(ennf_transformation,[],[f7])).
% 0.24/0.49  fof(f7,axiom,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 0.24/0.49  fof(f68,plain,(
% 0.24/0.49    k1_relat_1(sK2) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,k2_relat_1(sK2))),
% 0.24/0.49    inference(forward_demodulation,[],[f63,f60])).
% 0.24/0.49  fof(f60,plain,(
% 0.24/0.49    k1_relat_1(sK2) = k1_relset_1(sK1,k2_relat_1(sK2),sK2)),
% 0.24/0.49    inference(resolution,[],[f59,f26])).
% 0.24/0.49  fof(f26,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f12])).
% 0.24/0.49  fof(f12,plain,(
% 0.24/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.49    inference(ennf_transformation,[],[f2])).
% 0.24/0.49  fof(f2,axiom,(
% 0.24/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.24/0.49  fof(f63,plain,(
% 0.24/0.49    k1_relset_1(sK1,k2_relat_1(sK2),sK2) = k8_relset_1(sK1,k2_relat_1(sK2),sK2,k2_relat_1(sK2))),
% 0.24/0.49    inference(resolution,[],[f59,f29])).
% 0.24/0.49  fof(f29,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f14])).
% 0.24/0.49  fof(f14,plain,(
% 0.24/0.49    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.49    inference(ennf_transformation,[],[f8])).
% 0.24/0.49  fof(f8,axiom,(
% 0.24/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.24/0.49  fof(f55,plain,(
% 0.24/0.49    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.24/0.49    inference(backward_demodulation,[],[f50,f53])).
% 0.24/0.49  fof(f53,plain,(
% 0.24/0.49    k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 0.24/0.49    inference(superposition,[],[f52,f44])).
% 0.24/0.49  fof(f44,plain,(
% 0.24/0.49    ( ! [X0] : (k8_relset_1(sK1,sK0,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.24/0.49    inference(resolution,[],[f31,f22])).
% 0.24/0.49  fof(f52,plain,(
% 0.24/0.49    k8_relset_1(sK1,sK0,sK2,sK0) = k1_relat_1(sK2)),
% 0.24/0.49    inference(forward_demodulation,[],[f51,f37])).
% 0.24/0.49  fof(f37,plain,(
% 0.24/0.49    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.24/0.49    inference(resolution,[],[f26,f22])).
% 0.24/0.49  fof(f51,plain,(
% 0.24/0.49    k8_relset_1(sK1,sK0,sK2,sK0) = k1_relset_1(sK1,sK0,sK2)),
% 0.24/0.49    inference(resolution,[],[f29,f22])).
% 0.24/0.49  fof(f50,plain,(
% 0.24/0.49    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.24/0.49    inference(superposition,[],[f49,f44])).
% 0.24/0.49  fof(f49,plain,(
% 0.24/0.49    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.24/0.49    inference(backward_demodulation,[],[f45,f48])).
% 0.24/0.49  fof(f48,plain,(
% 0.24/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.24/0.49    inference(forward_demodulation,[],[f47,f39])).
% 0.24/0.49  fof(f39,plain,(
% 0.24/0.49    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.24/0.49    inference(resolution,[],[f27,f22])).
% 0.24/0.49  fof(f27,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f13])).
% 0.24/0.49  fof(f13,plain,(
% 0.24/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.49    inference(ennf_transformation,[],[f3])).
% 0.24/0.49  fof(f3,axiom,(
% 0.24/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.24/0.49  fof(f47,plain,(
% 0.24/0.49    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1)),
% 0.24/0.49    inference(forward_demodulation,[],[f46,f41])).
% 0.24/0.49  fof(f41,plain,(
% 0.24/0.49    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 0.24/0.49    inference(resolution,[],[f30,f22])).
% 0.24/0.49  fof(f30,plain,(
% 0.24/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f15])).
% 0.24/0.49  fof(f15,plain,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.24/0.49    inference(ennf_transformation,[],[f4])).
% 0.24/0.49  fof(f4,axiom,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.24/0.49  fof(f46,plain,(
% 0.24/0.49    k2_relset_1(sK1,sK0,sK2) = k7_relset_1(sK1,sK0,sK2,sK1)),
% 0.24/0.49    inference(resolution,[],[f28,f22])).
% 0.24/0.49  fof(f28,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f14])).
% 0.24/0.49  fof(f45,plain,(
% 0.24/0.49    k2_relat_1(sK2) != k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.24/0.49    inference(backward_demodulation,[],[f43,f44])).
% 0.24/0.49  fof(f43,plain,(
% 0.24/0.49    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | k2_relat_1(sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0))),
% 0.24/0.49    inference(forward_demodulation,[],[f42,f41])).
% 0.24/0.49  fof(f42,plain,(
% 0.24/0.49    k2_relat_1(sK2) != k9_relat_1(sK2,k8_relset_1(sK1,sK0,sK2,sK0)) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 0.24/0.49    inference(backward_demodulation,[],[f40,f41])).
% 0.24/0.49  fof(f40,plain,(
% 0.24/0.49    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)),
% 0.24/0.49    inference(backward_demodulation,[],[f38,f39])).
% 0.24/0.49  fof(f38,plain,(
% 0.24/0.49    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) | k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)),
% 0.24/0.49    inference(backward_demodulation,[],[f21,f37])).
% 0.24/0.49  fof(f21,plain,(
% 0.24/0.49    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)),
% 0.24/0.49    inference(cnf_transformation,[],[f11])).
% 0.24/0.49  fof(f99,plain,(
% 0.24/0.49    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.24/0.49    inference(superposition,[],[f85,f81])).
% 0.24/0.49  fof(f81,plain,(
% 0.24/0.49    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(k1_relat_1(sK2),sK0,sK2,X0)) )),
% 0.24/0.49    inference(resolution,[],[f75,f30])).
% 0.24/0.49  fof(f75,plain,(
% 0.24/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK0)))),
% 0.24/0.49    inference(resolution,[],[f69,f22])).
% 0.24/0.49  fof(f69,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))) )),
% 0.24/0.49    inference(resolution,[],[f33,f34])).
% 0.24/0.49  fof(f33,plain,(
% 0.24/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.24/0.49    inference(cnf_transformation,[],[f20])).
% 0.24/0.49  fof(f20,plain,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.24/0.49    inference(flattening,[],[f19])).
% 0.24/0.49  fof(f19,plain,(
% 0.24/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.24/0.49    inference(ennf_transformation,[],[f6])).
% 0.24/0.49  fof(f6,axiom,(
% 0.24/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.24/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.24/0.49  fof(f85,plain,(
% 0.24/0.49    k2_relat_1(sK2) = k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2))),
% 0.24/0.49    inference(forward_demodulation,[],[f79,f78])).
% 0.24/0.49  fof(f78,plain,(
% 0.24/0.49    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),sK0,sK2)),
% 0.24/0.49    inference(resolution,[],[f75,f27])).
% 0.24/0.49  fof(f79,plain,(
% 0.24/0.49    k2_relset_1(k1_relat_1(sK2),sK0,sK2) = k7_relset_1(k1_relat_1(sK2),sK0,sK2,k1_relat_1(sK2))),
% 0.24/0.49    inference(resolution,[],[f75,f28])).
% 0.24/0.49  % SZS output end Proof for theBenchmark
% 0.24/0.49  % (32637)------------------------------
% 0.24/0.49  % (32637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.49  % (32637)Termination reason: Refutation
% 0.24/0.49  
% 0.24/0.49  % (32637)Memory used [KB]: 1663
% 0.24/0.49  % (32637)Time elapsed: 0.055 s
% 0.24/0.49  % (32637)------------------------------
% 0.24/0.49  % (32637)------------------------------
% 0.24/0.49  % (32617)Success in time 0.11 s
%------------------------------------------------------------------------------
