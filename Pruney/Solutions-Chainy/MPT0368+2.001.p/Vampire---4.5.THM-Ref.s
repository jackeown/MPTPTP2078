%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:20 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 318 expanded)
%              Number of leaves         :    7 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :   87 ( 941 expanded)
%              Number of equality atoms :    9 ( 140 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f101,f101,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f101,plain,(
    r2_hidden(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f42,f92,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f92,plain,(
    r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f89,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f89,plain,(
    m1_subset_1(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f84,f84,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f84,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f56,f75,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    ~ m1_subset_1(sK3(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f57,f16])).

fof(f57,plain,(
    ~ r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f51,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f18,f42,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    r2_hidden(sK3(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f51,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f40,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f35,f17,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (3206)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (3222)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.17/0.51  % (3200)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.51  % (3206)Refutation not found, incomplete strategy% (3206)------------------------------
% 1.17/0.51  % (3206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (3206)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.51  
% 1.17/0.51  % (3206)Memory used [KB]: 10618
% 1.17/0.51  % (3206)Time elapsed: 0.102 s
% 1.17/0.51  % (3206)------------------------------
% 1.17/0.51  % (3206)------------------------------
% 1.17/0.51  % (3200)Refutation found. Thanks to Tanya!
% 1.17/0.51  % SZS status Theorem for theBenchmark
% 1.17/0.51  % SZS output start Proof for theBenchmark
% 1.17/0.51  fof(f142,plain,(
% 1.17/0.51    $false),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f101,f101,f30])).
% 1.17/0.51  fof(f30,plain,(
% 1.17/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f14])).
% 1.17/0.51  fof(f14,plain,(
% 1.17/0.51    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.17/0.51    inference(ennf_transformation,[],[f1])).
% 1.17/0.51  fof(f1,axiom,(
% 1.17/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.17/0.51  fof(f101,plain,(
% 1.17/0.51    r2_hidden(sK0,sK0)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f42,f92,f26])).
% 1.17/0.51  fof(f26,plain,(
% 1.17/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f12])).
% 1.17/0.51  fof(f12,plain,(
% 1.17/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.17/0.51    inference(ennf_transformation,[],[f2])).
% 1.17/0.51  fof(f2,axiom,(
% 1.17/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.17/0.51  fof(f92,plain,(
% 1.17/0.51    r2_hidden(sK0,sK1)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f89,f16])).
% 1.17/0.51  fof(f16,plain,(
% 1.17/0.51    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f11])).
% 1.17/0.51  fof(f11,plain,(
% 1.17/0.51    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/0.51    inference(flattening,[],[f10])).
% 1.17/0.51  fof(f10,plain,(
% 1.17/0.51    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/0.51    inference(ennf_transformation,[],[f9])).
% 1.17/0.51  fof(f9,negated_conjecture,(
% 1.17/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.17/0.51    inference(negated_conjecture,[],[f8])).
% 1.17/0.51  fof(f8,conjecture,(
% 1.17/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 1.17/0.51  fof(f89,plain,(
% 1.17/0.51    m1_subset_1(sK0,sK0)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f84,f84,f31])).
% 1.17/0.51  fof(f31,plain,(
% 1.17/0.51    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f15])).
% 1.17/0.51  fof(f15,plain,(
% 1.17/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.17/0.51    inference(ennf_transformation,[],[f5])).
% 1.17/0.51  fof(f5,axiom,(
% 1.17/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.17/0.51  fof(f84,plain,(
% 1.17/0.51    v1_xboole_0(sK0)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f56,f75,f33])).
% 1.17/0.51  fof(f33,plain,(
% 1.17/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f15])).
% 1.17/0.51  fof(f75,plain,(
% 1.17/0.51    ~m1_subset_1(sK3(sK0,sK1),sK0)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f57,f16])).
% 1.17/0.51  fof(f57,plain,(
% 1.17/0.51    ~r2_hidden(sK3(sK0,sK1),sK1)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f51,f28])).
% 1.17/0.51  fof(f28,plain,(
% 1.17/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f12])).
% 1.17/0.51  fof(f51,plain,(
% 1.17/0.51    ~r1_tarski(sK0,sK1)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f18,f42,f25])).
% 1.17/0.51  fof(f25,plain,(
% 1.17/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.17/0.51    inference(cnf_transformation,[],[f3])).
% 1.17/0.51  fof(f3,axiom,(
% 1.17/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.17/0.51  fof(f18,plain,(
% 1.17/0.51    sK0 != sK1),
% 1.17/0.51    inference(cnf_transformation,[],[f11])).
% 1.17/0.51  fof(f56,plain,(
% 1.17/0.51    r2_hidden(sK3(sK0,sK1),sK0)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f51,f27])).
% 1.17/0.51  fof(f27,plain,(
% 1.17/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f12])).
% 1.17/0.51  fof(f42,plain,(
% 1.17/0.51    r1_tarski(sK1,sK0)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f40,f36])).
% 1.17/0.51  fof(f36,plain,(
% 1.17/0.51    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.17/0.51    inference(equality_resolution,[],[f20])).
% 1.17/0.51  fof(f20,plain,(
% 1.17/0.51    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.17/0.51    inference(cnf_transformation,[],[f4])).
% 1.17/0.51  fof(f4,axiom,(
% 1.17/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.17/0.51  fof(f40,plain,(
% 1.17/0.52    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.17/0.52    inference(unit_resulting_resolution,[],[f35,f17,f34])).
% 1.17/0.52  fof(f34,plain,(
% 1.17/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f17,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.17/0.52    inference(cnf_transformation,[],[f11])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f6])).
% 1.17/0.52  fof(f6,axiom,(
% 1.17/0.52    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (3200)------------------------------
% 1.17/0.52  % (3200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (3200)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (3200)Memory used [KB]: 6268
% 1.17/0.52  % (3200)Time elapsed: 0.111 s
% 1.17/0.52  % (3200)------------------------------
% 1.17/0.52  % (3200)------------------------------
% 1.17/0.52  % (3195)Success in time 0.158 s
%------------------------------------------------------------------------------
