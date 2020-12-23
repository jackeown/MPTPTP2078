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
% DateTime   : Thu Dec  3 13:20:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  59 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :   88 ( 187 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f19])).

fof(f19,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f37,plain,(
    v1_xboole_0(k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f36,f25])).

fof(f25,plain,(
    k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f23,f15])).

fof(f15,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f23,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k1_tarski(X0) = k6_domain_1(sK0,X0) ) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f36,plain,(
    v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f34,f15])).

fof(f34,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f29,f16])).

fof(f16,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k6_domain_1(sK0,X0),sK0)
      | v1_xboole_0(k6_domain_1(sK0,X0))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f28,f18])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(k6_domain_1(sK0,X0))
      | ~ v1_subset_1(k6_domain_1(sK0,X0),sK0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f26,f18])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (14818)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.42  % (14818)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f37,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    v1_xboole_0(k1_tarski(sK1))),
% 0.21/0.42    inference(forward_demodulation,[],[f36,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.21/0.42    inference(resolution,[],[f23,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    m1_subset_1(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,sK0) | k1_tarski(X0) = k6_domain_1(sK0,X0)) )),
% 0.21/0.42    inference(resolution,[],[f21,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ~v1_xboole_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.21/0.42    inference(subsumption_resolution,[],[f34,f15])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.42    inference(resolution,[],[f29,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_subset_1(k6_domain_1(sK0,X0),sK0) | v1_xboole_0(k6_domain_1(sK0,X0)) | ~m1_subset_1(X0,sK0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f28,f18])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | ~v1_subset_1(k6_domain_1(sK0,X0),sK0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f27,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | ~v1_subset_1(X0,sK0)) )),
% 0.21/0.42    inference(subsumption_resolution,[],[f26,f18])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | ~v1_subset_1(X0,sK0)) )),
% 0.21/0.42    inference(resolution,[],[f20,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    v1_zfmisc_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (14818)------------------------------
% 0.21/0.42  % (14818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (14818)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (14818)Memory used [KB]: 10490
% 0.21/0.42  % (14818)Time elapsed: 0.006 s
% 0.21/0.42  % (14818)------------------------------
% 0.21/0.42  % (14818)------------------------------
% 0.21/0.42  % (14812)Success in time 0.064 s
%------------------------------------------------------------------------------
