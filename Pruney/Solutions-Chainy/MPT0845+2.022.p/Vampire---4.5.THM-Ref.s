%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  98 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 311 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f117])).

fof(f117,plain,(
    ! [X1] : ~ r2_hidden(sK3(sK0),X1) ),
    inference(subsumption_resolution,[],[f94,f116])).

fof(f116,plain,(
    ! [X0] : r1_xboole_0(sK0,X0) ),
    inference(subsumption_resolution,[],[f38,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r1_xboole_0(sK3(X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r1_xboole_0(sK3(X0),X0)
      | r1_xboole_0(sK3(X0),X0) ) ),
    inference(resolution,[],[f55,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(sK3(X0),X1),X0)
      | r1_xboole_0(X0,X2)
      | r1_xboole_0(sK3(X0),X1) ) ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK3(X1))
      | ~ r2_hidden(X0,X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,sK3(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK3(sK0),sK0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f27,f14])).

fof(f14,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

% (22511)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f27,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,X2)
      | r2_hidden(sK3(X1),X1) ) ),
    inference(resolution,[],[f19,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK3(X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f94,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(sK0),X1)
      | ~ r1_xboole_0(sK0,X1) ) ),
    inference(resolution,[],[f65,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(resolution,[],[f54,f29])).

fof(f29,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,X2)
      | r2_hidden(sK3(X2),X2) ) ),
    inference(resolution,[],[f20,f24])).

fof(f54,plain,(
    ~ r1_xboole_0(sK2(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f50,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(sK2(sK0,sK0),sK0) ),
    inference(resolution,[],[f35,f14])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f17,f16])).

fof(f16,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

% (22524)Termination reason: Refutation not found, incomplete strategy
fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

% (22524)Memory used [KB]: 1535
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

% (22524)Time elapsed: 0.054 s
% (22524)------------------------------
% (22524)------------------------------
% (22511)Refutation not found, incomplete strategy% (22511)------------------------------
% (22511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22511)Termination reason: Refutation not found, incomplete strategy

% (22511)Memory used [KB]: 6140
% (22511)Time elapsed: 0.049 s
% (22511)------------------------------
% (22511)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (22524)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (22528)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % (22516)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (22528)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (22524)Refutation not found, incomplete strategy% (22524)------------------------------
% 0.22/0.47  % (22524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f65,f117])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    ( ! [X1] : (~r2_hidden(sK3(sK0),X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f94,f116])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ( ! [X0] : (r1_xboole_0(sK0,X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f38,f115])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r1_xboole_0(sK3(X0),X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f114])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r1_xboole_0(sK3(X0),X0) | r1_xboole_0(sK3(X0),X0)) )),
% 0.22/0.47    inference(resolution,[],[f55,f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(rectify,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK1(sK3(X0),X1),X0) | r1_xboole_0(X0,X2) | r1_xboole_0(sK3(X0),X1)) )),
% 0.22/0.47    inference(resolution,[],[f32,f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK3(X1)) | ~r2_hidden(X0,X1) | r1_xboole_0(X1,X2)) )),
% 0.22/0.47    inference(resolution,[],[f23,f19])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,sK3(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_xboole_0(sK3(sK0),sK0) | r1_xboole_0(sK0,X0)) )),
% 0.22/0.47    inference(resolution,[],[f27,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  % (22511)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X1] : (r1_xboole_0(X1,X2) | r2_hidden(sK3(X1),X1)) )),
% 0.22/0.47    inference(resolution,[],[f19,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK3(X1),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    ( ! [X1] : (~r2_hidden(sK3(sK0),X1) | ~r1_xboole_0(sK0,X1)) )),
% 0.22/0.47    inference(resolution,[],[f65,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    r2_hidden(sK3(sK0),sK0)),
% 0.22/0.47    inference(resolution,[],[f54,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X1] : (r1_xboole_0(X1,X2) | r2_hidden(sK3(X2),X2)) )),
% 0.22/0.47    inference(resolution,[],[f20,f24])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ~r1_xboole_0(sK2(sK0,sK0),sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f50,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    k1_xboole_0 != sK0),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    k1_xboole_0 = sK0 | ~r1_xboole_0(sK2(sK0,sK0),sK0)),
% 0.22/0.47    inference(resolution,[],[f35,f14])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK2(X0,X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.47    inference(resolution,[],[f22,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f17,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  % (22524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  
% 0.22/0.47  % (22524)Memory used [KB]: 1535
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.22/0.47  % (22524)Time elapsed: 0.054 s
% 0.22/0.47  % (22524)------------------------------
% 0.22/0.47  % (22524)------------------------------
% 0.22/0.47  % (22511)Refutation not found, incomplete strategy% (22511)------------------------------
% 0.22/0.47  % (22511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22511)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (22511)Memory used [KB]: 6140
% 0.22/0.47  % (22511)Time elapsed: 0.049 s
% 0.22/0.47  % (22511)------------------------------
% 0.22/0.47  % (22511)------------------------------
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (22528)------------------------------
% 0.22/0.47  % (22528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22528)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (22528)Memory used [KB]: 1663
% 0.22/0.47  % (22528)Time elapsed: 0.060 s
% 0.22/0.47  % (22528)------------------------------
% 0.22/0.47  % (22528)------------------------------
% 0.22/0.47  % (22510)Success in time 0.115 s
%------------------------------------------------------------------------------
