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
% DateTime   : Thu Dec  3 12:56:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 121 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 283 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(subsumption_resolution,[],[f380,f340])).

fof(f340,plain,(
    r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(resolution,[],[f339,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(k6_relat_1(X0),X1)
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f149,f33])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f149,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f339,plain,(
    v5_relat_1(k6_relat_1(sK2),k2_relat_1(sK3)) ),
    inference(resolution,[],[f269,f91])).

fof(f91,plain,(
    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    inference(resolution,[],[f34,f79])).

fof(f79,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f29])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f57,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f269,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(sK3,k2_zfmisc_1(X11,X10))
      | v5_relat_1(k6_relat_1(sK2),X10) ) ),
    inference(resolution,[],[f216,f65])).

fof(f65,plain,(
    ! [X2] :
      ( r1_tarski(k6_relat_1(sK2),X2)
      | ~ r1_tarski(sK3,X2) ) ),
    inference(superposition,[],[f47,f61])).

fof(f61,plain,(
    sK3 = k2_xboole_0(k6_relat_1(sK2),sK3) ),
    inference(resolution,[],[f41,f30])).

fof(f30,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f51,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f380,plain,(
    ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f329,f378])).

fof(f378,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f49,f29])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f329,plain,(
    ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f326,f297])).

fof(f297,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f296,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f129,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)
      | ~ v4_relat_1(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f296,plain,(
    v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3)) ),
    inference(resolution,[],[f211,f91])).

fof(f211,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(sK3,k2_zfmisc_1(X8,X9))
      | v4_relat_1(k6_relat_1(sK2),X8) ) ),
    inference(resolution,[],[f180,f65])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f326,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f28,f322])).

fof(f322,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f48,f29])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f28,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (28316)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (28334)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (28334)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (28338)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.20/0.51  % (28330)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.20/0.51  % (28315)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f383,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f380,f340])).
% 1.20/0.52  fof(f340,plain,(
% 1.20/0.52    r1_tarski(sK2,k2_relat_1(sK3))),
% 1.20/0.52    inference(resolution,[],[f339,f152])).
% 1.20/0.52  fof(f152,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v5_relat_1(k6_relat_1(X0),X1) | r1_tarski(X0,X1)) )),
% 1.20/0.52    inference(forward_demodulation,[],[f149,f33])).
% 1.20/0.52  fof(f33,plain,(
% 1.20/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f11,axiom,(
% 1.20/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.20/0.52  fof(f149,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v5_relat_1(k6_relat_1(X0),X1)) )),
% 1.20/0.52    inference(resolution,[],[f40,f31])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,axiom,(
% 1.20/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.20/0.52  fof(f40,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.20/0.52  fof(f339,plain,(
% 1.20/0.52    v5_relat_1(k6_relat_1(sK2),k2_relat_1(sK3))),
% 1.20/0.52    inference(resolution,[],[f269,f91])).
% 1.20/0.52  fof(f91,plain,(
% 1.20/0.52    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 1.20/0.52    inference(resolution,[],[f34,f79])).
% 1.20/0.52  fof(f79,plain,(
% 1.20/0.52    v1_relat_1(sK3)),
% 1.20/0.52    inference(resolution,[],[f57,f29])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.20/0.52    inference(cnf_transformation,[],[f18])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(flattening,[],[f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(ennf_transformation,[],[f16])).
% 1.20/0.52  fof(f16,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 1.20/0.52    inference(negated_conjecture,[],[f15])).
% 1.20/0.52  fof(f15,conjecture,(
% 1.20/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 1.20/0.52  fof(f57,plain,(
% 1.20/0.52    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 1.20/0.52    inference(resolution,[],[f35,f36])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f9])).
% 1.20/0.52  fof(f9,axiom,(
% 1.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f20])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.20/0.52  fof(f34,plain,(
% 1.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,axiom,(
% 1.20/0.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 1.20/0.52  fof(f269,plain,(
% 1.20/0.52    ( ! [X10,X11] : (~r1_tarski(sK3,k2_zfmisc_1(X11,X10)) | v5_relat_1(k6_relat_1(sK2),X10)) )),
% 1.20/0.52    inference(resolution,[],[f216,f65])).
% 1.20/0.52  fof(f65,plain,(
% 1.20/0.52    ( ! [X2] : (r1_tarski(k6_relat_1(sK2),X2) | ~r1_tarski(sK3,X2)) )),
% 1.20/0.52    inference(superposition,[],[f47,f61])).
% 1.20/0.52  fof(f61,plain,(
% 1.20/0.52    sK3 = k2_xboole_0(k6_relat_1(sK2),sK3)),
% 1.20/0.52    inference(resolution,[],[f41,f30])).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    r1_tarski(k6_relat_1(sK2),sK3)),
% 1.20/0.52    inference(cnf_transformation,[],[f18])).
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.20/0.52  fof(f47,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f24])).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.20/0.52    inference(ennf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.20/0.52  fof(f216,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 1.20/0.52    inference(resolution,[],[f51,f45])).
% 1.20/0.52  fof(f45,plain,(
% 1.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.20/0.52  fof(f51,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f27])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(ennf_transformation,[],[f12])).
% 1.20/0.52  fof(f12,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.20/0.52  fof(f380,plain,(
% 1.20/0.52    ~r1_tarski(sK2,k2_relat_1(sK3))),
% 1.20/0.52    inference(backward_demodulation,[],[f329,f378])).
% 1.20/0.52  fof(f378,plain,(
% 1.20/0.52    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.20/0.52    inference(resolution,[],[f49,f29])).
% 1.20/0.52  fof(f49,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f26])).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(ennf_transformation,[],[f14])).
% 1.20/0.52  fof(f14,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.20/0.52  fof(f329,plain,(
% 1.20/0.52    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(subsumption_resolution,[],[f326,f297])).
% 1.20/0.52  fof(f297,plain,(
% 1.20/0.52    r1_tarski(sK2,k1_relat_1(sK3))),
% 1.20/0.52    inference(resolution,[],[f296,f132])).
% 1.20/0.52  fof(f132,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | r1_tarski(X0,X1)) )),
% 1.20/0.52    inference(forward_demodulation,[],[f129,f32])).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f129,plain,(
% 1.20/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) | ~v4_relat_1(k6_relat_1(X0),X1)) )),
% 1.20/0.52    inference(resolution,[],[f38,f31])).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f21])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.20/0.52  fof(f296,plain,(
% 1.20/0.52    v4_relat_1(k6_relat_1(sK2),k1_relat_1(sK3))),
% 1.20/0.52    inference(resolution,[],[f211,f91])).
% 1.20/0.52  fof(f211,plain,(
% 1.20/0.52    ( ! [X8,X9] : (~r1_tarski(sK3,k2_zfmisc_1(X8,X9)) | v4_relat_1(k6_relat_1(sK2),X8)) )),
% 1.20/0.52    inference(resolution,[],[f180,f65])).
% 1.20/0.52  fof(f180,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 1.20/0.52    inference(resolution,[],[f50,f45])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f27])).
% 1.20/0.52  fof(f326,plain,(
% 1.20/0.52    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(backward_demodulation,[],[f28,f322])).
% 1.20/0.52  fof(f322,plain,(
% 1.20/0.52    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.20/0.52    inference(resolution,[],[f48,f29])).
% 1.20/0.52  fof(f48,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f25])).
% 1.20/0.52  fof(f25,plain,(
% 1.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.20/0.52    inference(ennf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 1.20/0.52    inference(cnf_transformation,[],[f18])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (28334)------------------------------
% 1.20/0.52  % (28334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (28334)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (28334)Memory used [KB]: 1918
% 1.20/0.52  % (28334)Time elapsed: 0.084 s
% 1.20/0.52  % (28334)------------------------------
% 1.20/0.52  % (28334)------------------------------
% 1.20/0.52  % (28314)Success in time 0.159 s
%------------------------------------------------------------------------------
