%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:49 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   52 ( 100 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f21,f75])).

fof(f75,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f41,f73])).

fof(f73,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f62,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f62,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f47,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f20,f44])).

fof(f44,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f20,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f19,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f19,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:11:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (27065)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (27065)Refutation not found, incomplete strategy% (27065)------------------------------
% 0.21/0.51  % (27065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27065)Memory used [KB]: 10618
% 0.21/0.51  % (27065)Time elapsed: 0.091 s
% 0.21/0.51  % (27065)------------------------------
% 0.21/0.51  % (27065)------------------------------
% 1.24/0.52  % (27059)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.52  % (27059)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % (27064)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.53  % (27066)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f95,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(trivial_inequality_removal,[],[f94])).
% 1.24/0.53  fof(f94,plain,(
% 1.24/0.53    k1_xboole_0 != k1_xboole_0),
% 1.24/0.53    inference(superposition,[],[f21,f75])).
% 1.24/0.53  fof(f75,plain,(
% 1.24/0.53    k1_xboole_0 = sK1),
% 1.24/0.53    inference(backward_demodulation,[],[f41,f73])).
% 1.24/0.53  fof(f73,plain,(
% 1.24/0.53    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f62,f25])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.24/0.53  fof(f62,plain,(
% 1.24/0.53    r1_xboole_0(sK1,sK2)),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f47,f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f16])).
% 1.24/0.53  fof(f16,plain,(
% 1.24/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.24/0.53    inference(ennf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.24/0.53  fof(f47,plain,(
% 1.24/0.53    r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 1.24/0.53    inference(backward_demodulation,[],[f20,f44])).
% 1.24/0.53  fof(f44,plain,(
% 1.24/0.53    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f18,f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f15])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.24/0.53    inference(cnf_transformation,[],[f13])).
% 1.24/0.53  fof(f13,plain,(
% 1.24/0.53    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(flattening,[],[f12])).
% 1.24/0.53  fof(f12,plain,(
% 1.24/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f11])).
% 1.24/0.53  fof(f11,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.24/0.53    inference(negated_conjecture,[],[f10])).
% 1.24/0.53  fof(f10,conjecture,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 1.24/0.53  fof(f20,plain,(
% 1.24/0.53    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.24/0.53    inference(cnf_transformation,[],[f13])).
% 1.24/0.53  fof(f41,plain,(
% 1.24/0.53    sK1 = k3_xboole_0(sK1,sK2)),
% 1.24/0.53    inference(unit_resulting_resolution,[],[f19,f22])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f14,plain,(
% 1.24/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.24/0.53    inference(ennf_transformation,[],[f5])).
% 1.24/0.53  fof(f5,axiom,(
% 1.24/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.24/0.53  fof(f19,plain,(
% 1.24/0.53    r1_tarski(sK1,sK2)),
% 1.24/0.53    inference(cnf_transformation,[],[f13])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    k1_xboole_0 != sK1),
% 1.24/0.53    inference(cnf_transformation,[],[f13])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (27059)------------------------------
% 1.24/0.53  % (27059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (27059)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (27059)Memory used [KB]: 6140
% 1.24/0.53  % (27059)Time elapsed: 0.113 s
% 1.24/0.53  % (27059)------------------------------
% 1.24/0.53  % (27059)------------------------------
% 1.24/0.53  % (27054)Success in time 0.167 s
%------------------------------------------------------------------------------
