%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  91 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 260 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(subsumption_resolution,[],[f186,f59])).

fof(f59,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f58,f17])).

fof(f17,plain,(
    sK0 != sK1 ),
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

fof(f58,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f29,f55])).

fof(f55,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f53,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f49,f18])).

fof(f18,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f49,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f24,f16])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f186,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f182,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f182,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f174,f73])).

fof(f73,plain,(
    r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f72,f59])).

fof(f72,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f69,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | r1_tarski(sK0,sK1)
    | r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(resolution,[],[f65,f15])).

fof(f15,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0,sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f25,f16])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & m1_subset_1(X3,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & m1_subset_1(X3,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => r2_hidden(X3,X2) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_subset_1)).

fof(f174,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0,sK1),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f26,f16])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK2(X1,X2),X2)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:43:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (7227)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (7219)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (7227)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f186,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f58,f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    sK0 != sK1),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(flattening,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.22/0.56    inference(negated_conjecture,[],[f8])).
% 0.22/0.56  fof(f8,conjecture,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.22/0.56    inference(resolution,[],[f29,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    r1_tarski(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f53,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f49,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(resolution,[],[f24,f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    r1_tarski(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f182,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f20,f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | r1_tarski(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f174,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    r2_hidden(sK2(sK0,sK1),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f72,f59])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    r1_tarski(sK0,sK1) | r2_hidden(sK2(sK0,sK1),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f69,f38])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | r1_tarski(sK0,sK1) | r2_hidden(sK2(sK0,sK1),sK1)),
% 0.22/0.56    inference(resolution,[],[f65,f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(sK2(X0,sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK1)) )),
% 0.22/0.56    inference(resolution,[],[f25,f16])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(flattening,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & m1_subset_1(X3,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X1) => r2_hidden(X3,X2)) => r1_tarski(X1,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_subset_1)).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK1)) )),
% 0.22/0.56    inference(resolution,[],[f26,f16])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK2(X1,X2),X2) | r1_tarski(X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (7227)------------------------------
% 0.22/0.56  % (7227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (7227)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (7227)Memory used [KB]: 10746
% 0.22/0.56  % (7227)Time elapsed: 0.107 s
% 0.22/0.56  % (7227)------------------------------
% 0.22/0.56  % (7227)------------------------------
% 0.22/0.56  % (7204)Success in time 0.194 s
%------------------------------------------------------------------------------
