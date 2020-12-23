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
% DateTime   : Thu Dec  3 12:44:59 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 116 expanded)
%              Number of leaves         :   14 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :  129 ( 249 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2990,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2988,f1045])).

fof(f1045,plain,(
    ! [X2,X0,X1] : r2_hidden(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f186,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f186,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2988,plain,(
    ~ r2_hidden(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f428,f2985])).

fof(f2985,plain,(
    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f2933,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2933,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f2930,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f2930,plain,(
    r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f2926,f53])).

fof(f2926,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f2914,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2914,plain,(
    r1_tarski(k2_xboole_0(sK2,sK1),sK0) ),
    inference(superposition,[],[f2261,f87])).

fof(f87,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f79,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f79,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f75,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f26,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f2261,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f638,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f638,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),sK0) ),
    inference(unit_resulting_resolution,[],[f205,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f45,f113])).

fof(f113,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f88,f31])).

fof(f88,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f82,f36])).

fof(f82,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f76,f52])).

fof(f76,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f35])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f205,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) ),
    inference(unit_resulting_resolution,[],[f50,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f428,plain,(
    ~ r2_hidden(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f292,f419])).

fof(f419,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f26,f28,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f292,plain,(
    ~ r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f160,f288])).

fof(f288,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f37])).

fof(f160,plain,(
    ~ r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k3_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f27,f52])).

fof(f27,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (28308)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.45  % (28316)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (28316)Refutation not found, incomplete strategy% (28316)------------------------------
% 0.22/0.48  % (28316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28316)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28316)Memory used [KB]: 6140
% 0.22/0.48  % (28316)Time elapsed: 0.087 s
% 0.22/0.48  % (28316)------------------------------
% 0.22/0.48  % (28316)------------------------------
% 0.22/0.48  % (28329)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.48  % (28330)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.50  % (28305)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (28307)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (28306)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (28325)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (28315)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (28323)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (28313)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (28304)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (28322)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (28314)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (28303)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (28321)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (28326)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (28309)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (28310)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (28309)Refutation not found, incomplete strategy% (28309)------------------------------
% 0.22/0.53  % (28309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28320)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (28312)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (28314)Refutation not found, incomplete strategy% (28314)------------------------------
% 0.22/0.53  % (28314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28327)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (28328)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (28309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28309)Memory used [KB]: 10618
% 0.22/0.53  % (28309)Time elapsed: 0.118 s
% 0.22/0.53  % (28309)------------------------------
% 0.22/0.53  % (28309)------------------------------
% 0.22/0.54  % (28311)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (28317)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (28314)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28314)Memory used [KB]: 10618
% 0.22/0.54  % (28314)Time elapsed: 0.116 s
% 0.22/0.54  % (28314)------------------------------
% 0.22/0.54  % (28314)------------------------------
% 0.22/0.54  % (28319)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 2.14/0.64  % (28310)Refutation found. Thanks to Tanya!
% 2.14/0.64  % SZS status Theorem for theBenchmark
% 2.14/0.64  % SZS output start Proof for theBenchmark
% 2.14/0.64  fof(f2990,plain,(
% 2.14/0.64    $false),
% 2.14/0.64    inference(subsumption_resolution,[],[f2988,f1045])).
% 2.14/0.64  fof(f1045,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (r2_hidden(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_zfmisc_1(k4_xboole_0(X0,X1)))) )),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f186,f53])).
% 2.14/0.64  fof(f53,plain,(
% 2.14/0.64    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.14/0.64    inference(equality_resolution,[],[f41])).
% 2.14/0.64  fof(f41,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.14/0.64    inference(cnf_transformation,[],[f9])).
% 2.14/0.64  fof(f9,axiom,(
% 2.14/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.14/0.64  fof(f186,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f30,f46])).
% 2.14/0.64  fof(f46,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f21])).
% 2.14/0.64  fof(f21,plain,(
% 2.14/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.14/0.64    inference(ennf_transformation,[],[f5])).
% 2.14/0.64  fof(f5,axiom,(
% 2.14/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 2.14/0.64  fof(f30,plain,(
% 2.14/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f8])).
% 2.14/0.64  fof(f8,axiom,(
% 2.14/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.14/0.64  fof(f2988,plain,(
% 2.14/0.64    ~r2_hidden(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 2.14/0.64    inference(backward_demodulation,[],[f428,f2985])).
% 2.14/0.64  fof(f2985,plain,(
% 2.14/0.64    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.14/0.64    inference(unit_resulting_resolution,[],[f2933,f37])).
% 2.14/0.64  fof(f37,plain,(
% 2.14/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f19])).
% 2.14/0.64  fof(f19,plain,(
% 2.14/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.64    inference(ennf_transformation,[],[f11])).
% 2.14/0.64  fof(f11,axiom,(
% 2.14/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.14/0.65  fof(f2933,plain,(
% 2.14/0.65    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f29,f2930,f34])).
% 2.14/0.65  fof(f34,plain,(
% 2.14/0.65    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f17])).
% 2.14/0.65  fof(f17,plain,(
% 2.14/0.65    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f10])).
% 2.14/0.65  fof(f10,axiom,(
% 2.14/0.65    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.14/0.65  fof(f2930,plain,(
% 2.14/0.65    r2_hidden(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f2926,f53])).
% 2.14/0.65  fof(f2926,plain,(
% 2.14/0.65    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 2.14/0.65    inference(forward_demodulation,[],[f2914,f31])).
% 2.14/0.65  fof(f31,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f1])).
% 2.14/0.65  fof(f1,axiom,(
% 2.14/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.14/0.65  fof(f2914,plain,(
% 2.14/0.65    r1_tarski(k2_xboole_0(sK2,sK1),sK0)),
% 2.14/0.65    inference(superposition,[],[f2261,f87])).
% 2.14/0.65  fof(f87,plain,(
% 2.14/0.65    sK0 = k2_xboole_0(sK2,sK0)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f79,f36])).
% 2.14/0.65  fof(f36,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.14/0.65    inference(cnf_transformation,[],[f18])).
% 2.14/0.65  fof(f18,plain,(
% 2.14/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.14/0.65    inference(ennf_transformation,[],[f4])).
% 2.14/0.65  fof(f4,axiom,(
% 2.14/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.14/0.65  fof(f79,plain,(
% 2.14/0.65    r1_tarski(sK2,sK0)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f75,f52])).
% 2.14/0.65  fof(f52,plain,(
% 2.14/0.65    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.14/0.65    inference(equality_resolution,[],[f42])).
% 2.14/0.65  fof(f42,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.14/0.65    inference(cnf_transformation,[],[f9])).
% 2.14/0.65  fof(f75,plain,(
% 2.14/0.65    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f29,f26,f35])).
% 2.14/0.65  fof(f35,plain,(
% 2.14/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f17])).
% 2.14/0.65  fof(f26,plain,(
% 2.14/0.65    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.14/0.65    inference(cnf_transformation,[],[f16])).
% 2.14/0.65  fof(f16,plain,(
% 2.14/0.65    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.65    inference(ennf_transformation,[],[f15])).
% 2.14/0.65  fof(f15,negated_conjecture,(
% 2.14/0.65    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.14/0.65    inference(negated_conjecture,[],[f14])).
% 2.14/0.65  fof(f14,conjecture,(
% 2.14/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 2.14/0.65  fof(f2261,plain,(
% 2.14/0.65    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))) )),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f638,f48])).
% 2.14/0.65  fof(f48,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f23])).
% 2.14/0.65  fof(f23,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.14/0.65    inference(ennf_transformation,[],[f7])).
% 2.14/0.65  fof(f7,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.14/0.65  fof(f638,plain,(
% 2.14/0.65    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,sK1),X0),sK0)) )),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f205,f147])).
% 2.14/0.65  fof(f147,plain,(
% 2.14/0.65    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,sK0)) )),
% 2.14/0.65    inference(superposition,[],[f45,f113])).
% 2.14/0.65  fof(f113,plain,(
% 2.14/0.65    sK0 = k2_xboole_0(sK0,sK1)),
% 2.14/0.65    inference(superposition,[],[f88,f31])).
% 2.14/0.65  fof(f88,plain,(
% 2.14/0.65    sK0 = k2_xboole_0(sK1,sK0)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f82,f36])).
% 2.14/0.65  fof(f82,plain,(
% 2.14/0.65    r1_tarski(sK1,sK0)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f76,f52])).
% 2.14/0.65  fof(f76,plain,(
% 2.14/0.65    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f29,f28,f35])).
% 2.14/0.65  fof(f28,plain,(
% 2.14/0.65    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.14/0.65    inference(cnf_transformation,[],[f16])).
% 2.14/0.65  fof(f45,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f20])).
% 2.14/0.65  fof(f20,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.14/0.65    inference(ennf_transformation,[],[f3])).
% 2.14/0.65  fof(f3,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.14/0.65  fof(f205,plain,(
% 2.14/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1)) )),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f50,f47])).
% 2.14/0.65  fof(f47,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f22])).
% 2.14/0.65  fof(f22,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.14/0.65    inference(ennf_transformation,[],[f6])).
% 2.14/0.65  fof(f6,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.14/0.65  fof(f50,plain,(
% 2.14/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.14/0.65    inference(equality_resolution,[],[f39])).
% 2.14/0.65  fof(f39,plain,(
% 2.14/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.14/0.65    inference(cnf_transformation,[],[f2])).
% 2.14/0.65  fof(f2,axiom,(
% 2.14/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.65  fof(f29,plain,(
% 2.14/0.65    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f12])).
% 2.14/0.65  fof(f12,axiom,(
% 2.14/0.65    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.14/0.65  fof(f428,plain,(
% 2.14/0.65    ~r2_hidden(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 2.14/0.65    inference(backward_demodulation,[],[f292,f419])).
% 2.14/0.65  fof(f419,plain,(
% 2.14/0.65    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f26,f28,f49])).
% 2.14/0.65  fof(f49,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f25])).
% 2.14/0.65  fof(f25,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.14/0.65    inference(flattening,[],[f24])).
% 2.14/0.65  fof(f24,plain,(
% 2.14/0.65    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.14/0.65    inference(ennf_transformation,[],[f13])).
% 2.14/0.65  fof(f13,axiom,(
% 2.14/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.14/0.65  fof(f292,plain,(
% 2.14/0.65    ~r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))),
% 2.14/0.65    inference(backward_demodulation,[],[f160,f288])).
% 2.14/0.65  fof(f288,plain,(
% 2.14/0.65    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f28,f37])).
% 2.14/0.65  fof(f160,plain,(
% 2.14/0.65    ~r2_hidden(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(k3_subset_1(sK0,sK1)))),
% 2.14/0.65    inference(unit_resulting_resolution,[],[f27,f52])).
% 2.14/0.65  fof(f27,plain,(
% 2.14/0.65    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 2.14/0.65    inference(cnf_transformation,[],[f16])).
% 2.14/0.65  % SZS output end Proof for theBenchmark
% 2.14/0.65  % (28310)------------------------------
% 2.14/0.65  % (28310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.65  % (28310)Termination reason: Refutation
% 2.14/0.65  
% 2.14/0.65  % (28310)Memory used [KB]: 3198
% 2.14/0.65  % (28310)Time elapsed: 0.220 s
% 2.14/0.65  % (28310)------------------------------
% 2.14/0.65  % (28310)------------------------------
% 2.14/0.65  % (28299)Success in time 0.289 s
%------------------------------------------------------------------------------
