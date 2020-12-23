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
% DateTime   : Thu Dec  3 13:20:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  69 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   15
%              Number of atoms          :   75 ( 186 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(resolution,[],[f92,f30])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f92,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f17,f84])).

fof(f84,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f79,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f18,f77])).

fof(f77,plain,(
    ! [X2] :
      ( r1_tarski(sK0,X2)
      | k1_xboole_0 = k3_xboole_0(X2,sK0) ) ),
    inference(superposition,[],[f24,f54])).

fof(f54,plain,(
    ! [X1] :
      ( sK0 = k3_xboole_0(X1,sK0)
      | k1_xboole_0 = k3_xboole_0(X1,sK0) ) ),
    inference(superposition,[],[f53,f25])).

fof(f53,plain,(
    ! [X0] :
      ( sK0 = k3_xboole_0(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f41,f24])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f21,f40])).

fof(f40,plain,(
    sK0 = k1_tarski(sK2(sK0)) ),
    inference(forward_demodulation,[],[f39,f36])).

fof(f36,plain,(
    sK0 = k6_domain_1(sK0,sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f20,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f20,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f19,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    k6_domain_1(sK0,sK2(sK0)) = k1_tarski(sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f35,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f35,plain,(
    m1_subset_1(sK2(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f19,f20,f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f18,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (4402)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (4410)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (4426)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (4425)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (4405)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (4430)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (4405)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(resolution,[],[f92,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f17,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.52    inference(superposition,[],[f79,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f18,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X2] : (r1_tarski(sK0,X2) | k1_xboole_0 = k3_xboole_0(X2,sK0)) )),
% 0.20/0.52    inference(superposition,[],[f24,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X1] : (sK0 = k3_xboole_0(X1,sK0) | k1_xboole_0 = k3_xboole_0(X1,sK0)) )),
% 0.20/0.52    inference(superposition,[],[f53,f25])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (sK0 = k3_xboole_0(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f41,f24])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(superposition,[],[f21,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    sK0 = k1_tarski(sK2(sK0))),
% 0.20/0.52    inference(forward_demodulation,[],[f39,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    sK0 = k6_domain_1(sK0,sK2(sK0))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f19,f20,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    v1_zfmisc_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ~v1_xboole_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    k6_domain_1(sK0,sK2(sK0)) = k1_tarski(sK2(sK0))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f19,f35,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    m1_subset_1(sK2(sK0),sK0)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f19,f20,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ~r1_tarski(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (4405)------------------------------
% 0.20/0.52  % (4405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4405)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (4405)Memory used [KB]: 6268
% 0.20/0.52  % (4405)Time elapsed: 0.100 s
% 0.20/0.52  % (4405)------------------------------
% 0.20/0.52  % (4405)------------------------------
% 0.20/0.52  % (4400)Success in time 0.164 s
%------------------------------------------------------------------------------
