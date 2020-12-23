%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 141 expanded)
%              Number of leaves         :    6 (  28 expanded)
%              Depth                    :   19
%              Number of atoms          :  163 ( 521 expanded)
%              Number of equality atoms :   18 (  73 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(subsumption_resolution,[],[f212,f18])).

fof(f18,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

fof(f212,plain,(
    sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f211,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f211,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f210,f16])).

fof(f16,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f210,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f209,f15])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f209,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f205,f53])).

fof(f53,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f52,f15])).

fof(f52,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f51,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f51,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_subset_1(sK0,sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f24,f15])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f205,plain,
    ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(resolution,[],[f165,f65])).

fof(f65,plain,(
    ! [X1] :
      ( ~ r1_tarski(k3_subset_1(sK0,sK2),X1)
      | ~ r1_xboole_0(X1,sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k3_subset_1(sK0,sK2) = X1 ) ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_subset_1(sK0,sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f25,f15])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f165,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(sK0,X0),sK1)
      | ~ r1_xboole_0(k3_subset_1(sK0,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f132,f23])).

fof(f132,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ r1_xboole_0(X1,sK2)
      | r1_tarski(X1,sK1) ) ),
    inference(backward_demodulation,[],[f102,f116])).

fof(f116,plain,(
    sK2 = k3_subset_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f115,f15])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK2 = k3_subset_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f40,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f38,f16])).

fof(f38,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f37])).

fof(f37,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f113,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | sK2 = k3_subset_1(sK0,sK1) ),
    inference(resolution,[],[f112,f68])).

fof(f68,plain,(
    ! [X1] :
      ( ~ r1_tarski(k3_subset_1(sK0,sK1),X1)
      | ~ r1_xboole_0(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k3_subset_1(sK0,sK1) = X1 ) ),
    inference(resolution,[],[f61,f30])).

fof(f61,plain,(
    ! [X1] :
      ( r1_tarski(X1,k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ r1_xboole_0(X1,sK1) ) ),
    inference(resolution,[],[f25,f19])).

fof(f112,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f111,f19])).

fof(f111,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f105,f23])).

fof(f105,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f101,f17])).

fof(f17,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK2))
      | r1_tarski(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f27,f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f102,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(X1,sK1)
      | ~ r1_xboole_0(X1,k3_subset_1(sK0,sK1)) ) ),
    inference(resolution,[],[f27,f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:22:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (20154)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.46  % (20170)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.46  % (20170)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (20154)Refutation not found, incomplete strategy% (20154)------------------------------
% 0.22/0.48  % (20154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f213,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f212,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    sK1 != k3_subset_1(sK0,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    sK1 = k3_subset_1(sK0,sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f211,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f210,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    r1_xboole_0(sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f209,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f209,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f205,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f52,f15])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(resolution,[],[f51,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.22/0.48    inference(resolution,[],[f48,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(X0,k3_subset_1(sK0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_xboole_0(X0,sK2)) )),
% 0.22/0.48    inference(resolution,[],[f24,f15])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    ~r1_xboole_0(k3_subset_1(sK0,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | sK1 = k3_subset_1(sK0,sK2)),
% 0.22/0.48    inference(resolution,[],[f165,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X1] : (~r1_tarski(k3_subset_1(sK0,sK2),X1) | ~r1_xboole_0(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k3_subset_1(sK0,sK2) = X1) )),
% 0.22/0.48    inference(resolution,[],[f60,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(X0,k3_subset_1(sK0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r1_xboole_0(X0,sK2)) )),
% 0.22/0.48    inference(resolution,[],[f25,f15])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k3_subset_1(sK0,X0),sK1) | ~r1_xboole_0(k3_subset_1(sK0,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.22/0.48    inference(resolution,[],[f132,f23])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~r1_xboole_0(X1,sK2) | r1_tarski(X1,sK1)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f102,f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    sK2 = k3_subset_1(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f115,f15])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sK2 = k3_subset_1(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f113,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    r1_xboole_0(sK2,sK1)),
% 0.22/0.48    inference(resolution,[],[f38,f16])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.48    inference(resolution,[],[f33,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(resolution,[],[f20,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ~r1_xboole_0(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | sK2 = k3_subset_1(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f112,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X1] : (~r1_tarski(k3_subset_1(sK0,sK1),X1) | ~r1_xboole_0(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k3_subset_1(sK0,sK1) = X1) )),
% 0.22/0.48    inference(resolution,[],[f61,f30])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(X1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~r1_xboole_0(X1,sK1)) )),
% 0.22/0.48    inference(resolution,[],[f25,f19])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f111,f19])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(resolution,[],[f105,f23])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.22/0.48    inference(resolution,[],[f101,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK2)) | r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.22/0.48    inference(resolution,[],[f27,f15])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(X1,sK1) | ~r1_xboole_0(X1,k3_subset_1(sK0,sK1))) )),
% 0.22/0.48    inference(resolution,[],[f27,f19])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (20170)------------------------------
% 0.22/0.48  % (20170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20170)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (20170)Memory used [KB]: 1663
% 0.22/0.48  % (20170)Time elapsed: 0.070 s
% 0.22/0.48  % (20170)------------------------------
% 0.22/0.48  % (20170)------------------------------
% 0.22/0.48  % (20144)Success in time 0.117 s
%------------------------------------------------------------------------------
