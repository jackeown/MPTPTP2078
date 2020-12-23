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
% DateTime   : Thu Dec  3 12:44:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 132 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :   18
%              Number of atoms          :  138 ( 383 expanded)
%              Number of equality atoms :   17 (  54 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(subsumption_resolution,[],[f327,f65])).

fof(f65,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f61,f20])).

fof(f20,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f61,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK2)
      | r1_tarski(X4,sK0) ) ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f54,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | r1_tarski(sK2,sK0) ) ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f52,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(sK0))
      | r1_tarski(sK2,sK0) ) ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f49,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f47,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f327,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f326,f43])).

fof(f326,plain,(
    ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f325,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f325,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f322,f20])).

fof(f322,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f314,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_subset_1(X1,X0))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_subset_1(X0) = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

% (8409)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f314,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_subset_1(sK0,sK1))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f310,f38])).

fof(f310,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f301,f65])).

fof(f301,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f293,f21])).

fof(f21,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f293,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_subset_1(sK0,sK2))
      | r1_tarski(sK2,k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f292,f43])).

fof(f292,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | r1_tarski(sK2,k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK2)) ) ),
    inference(resolution,[],[f289,f44])).

fof(f289,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK2))
      | r1_tarski(sK2,k3_subset_1(sK0,X0)) ) ),
    inference(resolution,[],[f33,f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (8412)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (8428)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (8420)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (8430)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (8422)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (8414)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (8428)Refutation not found, incomplete strategy% (8428)------------------------------
% 0.21/0.56  % (8428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8412)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (8428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8428)Memory used [KB]: 10746
% 0.21/0.56  % (8428)Time elapsed: 0.145 s
% 0.21/0.56  % (8428)------------------------------
% 0.21/0.56  % (8428)------------------------------
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f328,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f327,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    r1_tarski(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f61,f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    r1_tarski(sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X4] : (~r1_tarski(X4,sK2) | r1_tarski(X4,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f38,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    r1_tarski(sK2,sK0)),
% 0.21/0.57    inference(resolution,[],[f54,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(sK2,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f52,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_hidden(X2,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f49,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK0)),
% 0.21/0.57    inference(resolution,[],[f47,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.21/0.57    inference(equality_resolution,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f30,f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.57  fof(f327,plain,(
% 0.21/0.57    ~r1_tarski(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f326,f43])).
% 0.21/0.57  fof(f326,plain,(
% 0.21/0.57    ~r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f325,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f325,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | ~r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f322,f20])).
% 0.21/0.57  fof(f322,plain,(
% 0.21/0.57    ~r1_tarski(sK1,sK2) | k1_xboole_0 = sK1 | ~r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f314,f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k3_subset_1(X1,X0)) | k1_xboole_0 = X0 | ~r2_hidden(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.57    inference(resolution,[],[f39,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f29,f26])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f32,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  % (8409)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.57  fof(f314,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(X0,k3_subset_1(sK0,sK1)) | ~r1_tarski(X0,sK2)) )),
% 0.21/0.57    inference(resolution,[],[f310,f38])).
% 0.21/0.57  fof(f310,plain,(
% 0.21/0.57    r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.21/0.57    inference(subsumption_resolution,[],[f301,f65])).
% 0.21/0.57  fof(f301,plain,(
% 0.21/0.57    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f293,f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k3_subset_1(sK0,sK2)) | r1_tarski(sK2,k3_subset_1(sK0,X0)) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.57    inference(resolution,[],[f292,f43])).
% 0.21/0.57  fof(f292,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_subset_1(sK0,X0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK2))) )),
% 0.21/0.57    inference(resolution,[],[f289,f44])).
% 0.21/0.57  fof(f289,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK2)) | r1_tarski(sK2,k3_subset_1(sK0,X0))) )),
% 0.21/0.57    inference(resolution,[],[f33,f19])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (8412)------------------------------
% 0.21/0.57  % (8412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8412)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (8412)Memory used [KB]: 6524
% 0.21/0.57  % (8412)Time elapsed: 0.145 s
% 0.21/0.57  % (8412)------------------------------
% 0.21/0.57  % (8412)------------------------------
% 0.21/0.57  % (8405)Success in time 0.208 s
%------------------------------------------------------------------------------
