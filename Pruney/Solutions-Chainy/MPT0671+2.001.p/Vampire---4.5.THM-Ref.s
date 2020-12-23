%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  49 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 122 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(resolution,[],[f30,f15])).

fof(f15,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_funct_1)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f29,f26])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(subsumption_resolution,[],[f25,f13])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | v1_relat_1(k8_relat_1(X0,sK1)) ) ),
    inference(resolution,[],[f18,f23])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k8_relat_1(X0,sK1),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,sK1),sK1) ),
    inference(resolution,[],[f19,f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

% (14672)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k8_relat_1(X0,sK1))
      | r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f28,f13])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k8_relat_1(X0,sK1))
      | r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f16,f22])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14677)WARNING: option uwaf not known.
% 0.22/0.51  % (14675)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (14673)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.51  % (14676)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.51  % (14686)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.51  % (14669)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.51  % (14673)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f30,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(k8_relat_1(sK0,sK1)),k1_relat_1(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0,X1] : (~r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k1_relat_1(k8_relat_1(X0,X1)),k1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_funct_1)).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f29,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f25,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    v1_relat_1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(sK1) | v1_relat_1(k8_relat_1(X0,sK1))) )),
% 0.22/0.51    inference(resolution,[],[f18,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k8_relat_1(X0,sK1),k1_zfmisc_1(sK1))) )),
% 0.22/0.51    inference(resolution,[],[f20,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),sK1)) )),
% 0.22/0.51    inference(resolution,[],[f19,f13])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k8_relat_1(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.51  % (14672)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(k8_relat_1(X0,sK1)) | r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f28,f13])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(X0,sK1)) | r1_tarski(k1_relat_1(k8_relat_1(X0,sK1)),k1_relat_1(sK1))) )),
% 0.22/0.51    inference(resolution,[],[f16,f22])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (14673)------------------------------
% 0.22/0.51  % (14673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14673)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (14673)Memory used [KB]: 5245
% 0.22/0.51  % (14673)Time elapsed: 0.087 s
% 0.22/0.51  % (14673)------------------------------
% 0.22/0.51  % (14673)------------------------------
% 0.22/0.51  % (14680)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (14666)Success in time 0.151 s
%------------------------------------------------------------------------------
