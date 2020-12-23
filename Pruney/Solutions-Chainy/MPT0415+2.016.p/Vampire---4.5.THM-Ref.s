%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 175 expanded)
%              Number of leaves         :    7 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 486 expanded)
%              Number of equality atoms :   31 ( 216 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f250,f88])).

fof(f88,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f81,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f81,plain,(
    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f80,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f50,f15])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | k1_xboole_0 = X0
      | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f49,f17])).

fof(f17,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0))
      | k7_setfam_1(sK0,sK1) = X0 ) ),
    inference(resolution,[],[f26,f15])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0))
      | k7_setfam_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f250,plain,(
    ~ m1_subset_1(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f248,f120])).

fof(f120,plain,(
    r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f117,f81])).

fof(f117,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_subset_1(sK0,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f18,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f18,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(k3_subset_1(sK0,X0),sK1) ) ),
    inference(forward_demodulation,[],[f46,f17])).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(k3_subset_1(sK0,X0),sK1)
      | r2_hidden(X0,k7_setfam_1(sK0,sK1)) ) ),
    inference(resolution,[],[f35,f15])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ r2_hidden(k3_subset_1(X0,X3),X1)
      | r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,
    ( r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f85,f16])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    inference(resolution,[],[f52,f15])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | k1_xboole_0 = X0
      | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X0)),sK1)
      | r2_hidden(sK2(sK0,sK1,X0),X0) ) ),
    inference(forward_demodulation,[],[f51,f17])).

fof(f51,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X0)),sK1)
      | r2_hidden(sK2(sK0,sK1,X0),X0)
      | k7_setfam_1(sK0,sK1) = X0 ) ),
    inference(resolution,[],[f22,f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k7_setfam_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f248,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f48,f87])).

fof(f87,plain,(
    sK2(sK0,sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK2(sK0,sK1,sK1))) ),
    inference(resolution,[],[f81,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:31:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (2033)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (2032)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (2033)Refutation not found, incomplete strategy% (2033)------------------------------
% 0.22/0.48  % (2033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (2051)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (2050)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (2033)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (2033)Memory used [KB]: 10618
% 0.22/0.49  % (2033)Time elapsed: 0.063 s
% 0.22/0.49  % (2033)------------------------------
% 0.22/0.49  % (2033)------------------------------
% 0.22/0.49  % (2036)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (2047)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (2049)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (2037)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (2048)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (2050)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f250,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    m1_subset_1(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f81,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f80,f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f7])).
% 0.22/0.50  fof(f7,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f50,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = X0 | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f49,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(sK2(sK0,sK1,X0),k1_zfmisc_1(sK0)) | k7_setfam_1(sK0,sK1) = X0) )),
% 0.22/0.50    inference(resolution,[],[f26,f15])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(X0)) | k7_setfam_1(X0,X1) = X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    ~m1_subset_1(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f248,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f81])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f86,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k3_subset_1(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f47,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(superposition,[],[f18,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(k3_subset_1(sK0,X0),sK1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f46,f17])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(k3_subset_1(sK0,X0),sK1) | r2_hidden(X0,k7_setfam_1(sK0,sK1))) )),
% 0.22/0.50    inference(resolution,[],[f35,f15])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f31,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f16])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),sK1) | r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.22/0.50    inference(resolution,[],[f52,f15])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = X0 | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X0)),sK1) | r2_hidden(sK2(sK0,sK1,X0),X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f51,f17])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | r2_hidden(k3_subset_1(sK0,sK2(sK0,sK1,X0)),sK1) | r2_hidden(sK2(sK0,sK1,X0),X0) | k7_setfam_1(sK0,sK1) = X0) )),
% 0.22/0.50    inference(resolution,[],[f22,f15])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(k3_subset_1(X0,sK2(X0,X1,X2)),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k7_setfam_1(X0,X1) = X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(k3_subset_1(sK0,sK2(sK0,sK1,sK1)),k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(superposition,[],[f48,f87])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    sK2(sK0,sK1,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,sK2(sK0,sK1,sK1)))),
% 0.22/0.50    inference(resolution,[],[f81,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (2050)------------------------------
% 0.22/0.50  % (2050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2050)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (2050)Memory used [KB]: 1791
% 0.22/0.50  % (2050)Time elapsed: 0.077 s
% 0.22/0.50  % (2050)------------------------------
% 0.22/0.50  % (2050)------------------------------
% 0.22/0.50  % (2029)Success in time 0.138 s
%------------------------------------------------------------------------------
