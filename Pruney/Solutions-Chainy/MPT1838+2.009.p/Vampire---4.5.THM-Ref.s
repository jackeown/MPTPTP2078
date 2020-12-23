%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:55 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 133 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 427 expanded)
%              Number of equality atoms :   43 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f429,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f428])).

fof(f428,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f426,f78])).

fof(f78,plain,(
    sK1 = k1_tarski(sK3(sK1)) ),
    inference(forward_demodulation,[],[f77,f61])).

fof(f61,plain,(
    sK1 = k6_domain_1(sK1,sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f28,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK3(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f28,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f27,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f60,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f60,plain,(
    m1_subset_1(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f27,f28,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f426,plain,(
    ! [X0] : k1_tarski(X0) != sK1 ),
    inference(forward_demodulation,[],[f425,f65])).

fof(f65,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f425,plain,(
    ! [X0] : k1_tarski(X0) != k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f155,f30,f418,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) != k1_tarski(X0)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f418,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f54,f123])).

fof(f123,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK4(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f84,f32])).

fof(f84,plain,(
    r1_tarski(k1_tarski(sK4(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f62,plain,(
    r2_hidden(sK4(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f31,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f155,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f144,f65])).

fof(f144,plain,(
    ! [X0] : k1_xboole_0 != k2_xboole_0(X0,sK1) ),
    inference(superposition,[],[f115,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 != k2_xboole_0(sK1,X0) ),
    inference(superposition,[],[f54,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:51:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (30926)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (30923)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (30942)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (30922)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (30947)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (30920)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (30933)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (30932)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (30934)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (30939)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (30948)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.53  % (30925)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.53  % (30946)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.53  % (30923)Refutation found. Thanks to Tanya!
% 1.33/0.53  % SZS status Theorem for theBenchmark
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  fof(f429,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(trivial_inequality_removal,[],[f428])).
% 1.33/0.53  fof(f428,plain,(
% 1.33/0.53    sK1 != sK1),
% 1.33/0.53    inference(superposition,[],[f426,f78])).
% 1.33/0.53  fof(f78,plain,(
% 1.33/0.53    sK1 = k1_tarski(sK3(sK1))),
% 1.33/0.53    inference(forward_demodulation,[],[f77,f61])).
% 1.33/0.53  fof(f61,plain,(
% 1.33/0.53    sK1 = k6_domain_1(sK1,sK3(sK1))),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f27,f28,f42])).
% 1.33/0.53  fof(f42,plain,(
% 1.33/0.53    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK3(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f23])).
% 1.33/0.53  fof(f23,plain,(
% 1.33/0.53    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f15])).
% 1.33/0.53  fof(f15,axiom,(
% 1.33/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.33/0.53  fof(f28,plain,(
% 1.33/0.53    v1_zfmisc_1(sK1)),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.33/0.53    inference(flattening,[],[f18])).
% 1.33/0.53  fof(f18,plain,(
% 1.33/0.53    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f17])).
% 1.33/0.53  fof(f17,negated_conjecture,(
% 1.33/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.33/0.53    inference(negated_conjecture,[],[f16])).
% 1.33/0.53  fof(f16,conjecture,(
% 1.33/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ~v1_xboole_0(sK1)),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f77,plain,(
% 1.33/0.53    k6_domain_1(sK1,sK3(sK1)) = k1_tarski(sK3(sK1))),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f27,f60,f53])).
% 1.33/0.53  fof(f53,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.33/0.53    inference(flattening,[],[f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f14])).
% 1.33/0.53  fof(f14,axiom,(
% 1.33/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.33/0.53  fof(f60,plain,(
% 1.33/0.53    m1_subset_1(sK3(sK1),sK1)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f27,f28,f41])).
% 1.33/0.53  fof(f41,plain,(
% 1.33/0.53    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f23])).
% 1.33/0.53  fof(f426,plain,(
% 1.33/0.53    ( ! [X0] : (k1_tarski(X0) != sK1) )),
% 1.33/0.53    inference(forward_demodulation,[],[f425,f65])).
% 1.33/0.53  fof(f65,plain,(
% 1.33/0.53    sK1 = k2_xboole_0(sK0,sK1)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f29,f32])).
% 1.33/0.53  fof(f32,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f20])).
% 1.33/0.53  fof(f20,plain,(
% 1.33/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.33/0.53    inference(ennf_transformation,[],[f6])).
% 1.33/0.53  fof(f6,axiom,(
% 1.33/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.33/0.53  fof(f29,plain,(
% 1.33/0.53    r1_tarski(sK0,sK1)),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f425,plain,(
% 1.33/0.53    ( ! [X0] : (k1_tarski(X0) != k2_xboole_0(sK0,sK1)) )),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f155,f30,f418,f52])).
% 1.33/0.53  fof(f52,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) != k1_tarski(X0) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.33/0.53    inference(cnf_transformation,[],[f24])).
% 1.33/0.53  fof(f24,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f12])).
% 1.33/0.53  fof(f12,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.33/0.53  fof(f418,plain,(
% 1.33/0.53    k1_xboole_0 != sK0),
% 1.33/0.53    inference(superposition,[],[f54,f123])).
% 1.33/0.53  fof(f123,plain,(
% 1.33/0.53    sK0 = k2_xboole_0(k1_tarski(sK4(sK0)),sK0)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f84,f32])).
% 1.33/0.53  fof(f84,plain,(
% 1.33/0.53    r1_tarski(k1_tarski(sK4(sK0)),sK0)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f62,f35])).
% 1.33/0.53  fof(f35,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f11])).
% 1.33/0.53  fof(f11,axiom,(
% 1.33/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.33/0.53  fof(f62,plain,(
% 1.33/0.53    r2_hidden(sK4(sK0),sK0)),
% 1.33/0.53    inference(unit_resulting_resolution,[],[f31,f44])).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f2])).
% 1.33/0.53  fof(f2,axiom,(
% 1.33/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.33/0.53  fof(f31,plain,(
% 1.33/0.53    ~v1_xboole_0(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f54,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f13])).
% 1.33/0.53  fof(f13,axiom,(
% 1.33/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.33/0.53  fof(f30,plain,(
% 1.33/0.53    sK0 != sK1),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f155,plain,(
% 1.33/0.53    k1_xboole_0 != sK1),
% 1.33/0.53    inference(superposition,[],[f144,f65])).
% 1.33/0.53  fof(f144,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(X0,sK1)) )),
% 1.33/0.53    inference(superposition,[],[f115,f33])).
% 1.33/0.53  fof(f33,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f1])).
% 1.33/0.53  fof(f1,axiom,(
% 1.33/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.33/0.53  fof(f115,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(sK1,X0)) )),
% 1.33/0.53    inference(superposition,[],[f54,f78])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (30923)------------------------------
% 1.33/0.53  % (30923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (30923)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (30923)Memory used [KB]: 6396
% 1.33/0.53  % (30923)Time elapsed: 0.122 s
% 1.33/0.53  % (30923)------------------------------
% 1.33/0.53  % (30923)------------------------------
% 1.33/0.53  % (30935)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.53  % (30919)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.53  % (30918)Success in time 0.172 s
%------------------------------------------------------------------------------
