%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:17 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 (  82 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   14
%              Number of atoms          :   88 ( 228 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(subsumption_resolution,[],[f233,f120])).

fof(f120,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f34,f107])).

fof(f107,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f87,f28])).

fof(f28,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f22,f15])).

fof(f15,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(sK3,k3_xboole_0(X1,sK2)) ),
    inference(superposition,[],[f74,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f74,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK3,X3),sK2) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK3,X3),sK2) ) ),
    inference(superposition,[],[f34,f61])).

fof(f61,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK3,X7)) ),
    inference(forward_demodulation,[],[f55,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f22,f20])).

% (30594)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
fof(f20,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f55,plain,(
    ! [X7] : k3_xboole_0(sK2,k3_xboole_0(sK3,X7)) = k3_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f233,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f232,f25])).

fof(f232,plain,(
    ~ r1_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f231,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f231,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f227,f14])).

fof(f14,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f227,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 12:53:14 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.37  % (30599)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.18/0.40  % (30600)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.18/0.40  % (30598)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.18/0.41  % (30593)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.18/0.42  % (30603)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.18/0.42  % (30593)Refutation found. Thanks to Tanya!
% 0.18/0.42  % SZS status Theorem for theBenchmark
% 0.18/0.42  % SZS output start Proof for theBenchmark
% 0.18/0.42  fof(f235,plain,(
% 0.18/0.42    $false),
% 0.18/0.42    inference(subsumption_resolution,[],[f233,f120])).
% 0.18/0.42  fof(f120,plain,(
% 0.18/0.42    k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.18/0.42    inference(trivial_inequality_removal,[],[f119])).
% 0.18/0.42  fof(f119,plain,(
% 0.18/0.42    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.18/0.42    inference(superposition,[],[f34,f107])).
% 0.18/0.42  fof(f107,plain,(
% 0.18/0.42    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 0.18/0.42    inference(superposition,[],[f87,f28])).
% 0.18/0.42  fof(f28,plain,(
% 0.18/0.42    sK1 = k3_xboole_0(sK1,sK2)),
% 0.18/0.42    inference(resolution,[],[f22,f15])).
% 0.18/0.42  fof(f15,plain,(
% 0.18/0.42    r1_tarski(sK1,sK2)),
% 0.18/0.42    inference(cnf_transformation,[],[f10])).
% 0.18/0.42  fof(f10,plain,(
% 0.18/0.42    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.42    inference(flattening,[],[f9])).
% 0.18/0.42  fof(f9,plain,(
% 0.18/0.42    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f8])).
% 0.18/0.42  fof(f8,negated_conjecture,(
% 0.18/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.18/0.42    inference(negated_conjecture,[],[f7])).
% 0.18/0.42  fof(f7,conjecture,(
% 0.18/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).
% 0.18/0.42  fof(f22,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.18/0.42    inference(cnf_transformation,[],[f12])).
% 0.18/0.42  fof(f12,plain,(
% 0.18/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.42    inference(ennf_transformation,[],[f4])).
% 0.18/0.42  fof(f4,axiom,(
% 0.18/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.18/0.42  fof(f87,plain,(
% 0.18/0.42    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK3,k3_xboole_0(X1,sK2))) )),
% 0.18/0.42    inference(superposition,[],[f74,f27])).
% 0.18/0.42  fof(f27,plain,(
% 0.18/0.42    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.18/0.42    inference(cnf_transformation,[],[f3])).
% 0.18/0.42  fof(f3,axiom,(
% 0.18/0.42    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.18/0.42  fof(f74,plain,(
% 0.18/0.42    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK3,X3),sK2)) )),
% 0.18/0.42    inference(trivial_inequality_removal,[],[f73])).
% 0.18/0.42  fof(f73,plain,(
% 0.18/0.42    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK3,X3),sK2)) )),
% 0.18/0.42    inference(superposition,[],[f34,f61])).
% 0.18/0.42  fof(f61,plain,(
% 0.18/0.42    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK3,X7))) )),
% 0.18/0.42    inference(forward_demodulation,[],[f55,f29])).
% 0.18/0.42  fof(f29,plain,(
% 0.18/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.18/0.42    inference(resolution,[],[f22,f20])).
% 0.18/0.42  % (30594)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.18/0.42  fof(f20,plain,(
% 0.18/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f5])).
% 0.18/0.42  fof(f5,axiom,(
% 0.18/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.42  fof(f55,plain,(
% 0.18/0.42    ( ! [X7] : (k3_xboole_0(sK2,k3_xboole_0(sK3,X7)) = k3_xboole_0(k1_xboole_0,X7)) )),
% 0.18/0.42    inference(superposition,[],[f27,f33])).
% 0.18/0.42  fof(f33,plain,(
% 0.18/0.42    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.18/0.42    inference(resolution,[],[f32,f16])).
% 0.18/0.42  fof(f16,plain,(
% 0.18/0.42    r1_xboole_0(sK3,sK2)),
% 0.18/0.42    inference(cnf_transformation,[],[f10])).
% 0.18/0.42  fof(f32,plain,(
% 0.18/0.42    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | k1_xboole_0 = k3_xboole_0(X2,X3)) )),
% 0.18/0.42    inference(resolution,[],[f26,f21])).
% 0.18/0.42  fof(f21,plain,(
% 0.18/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f11])).
% 0.18/0.42  fof(f11,plain,(
% 0.18/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.18/0.42    inference(ennf_transformation,[],[f2])).
% 0.18/0.42  fof(f2,axiom,(
% 0.18/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.18/0.42  fof(f26,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.18/0.42    inference(cnf_transformation,[],[f1])).
% 0.18/0.42  fof(f1,axiom,(
% 0.18/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.18/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.18/0.42  fof(f34,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(X1,X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.18/0.42    inference(resolution,[],[f32,f25])).
% 0.18/0.42  fof(f25,plain,(
% 0.18/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.18/0.42    inference(cnf_transformation,[],[f1])).
% 0.18/0.42  fof(f233,plain,(
% 0.18/0.42    k1_xboole_0 != k3_xboole_0(sK1,sK3)),
% 0.18/0.42    inference(resolution,[],[f232,f25])).
% 0.18/0.42  fof(f232,plain,(
% 0.18/0.42    ~r1_xboole_0(sK1,sK3)),
% 0.18/0.42    inference(subsumption_resolution,[],[f231,f19])).
% 0.18/0.42  fof(f19,plain,(
% 0.18/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.18/0.42    inference(cnf_transformation,[],[f10])).
% 0.18/0.42  fof(f231,plain,(
% 0.18/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,sK3)),
% 0.18/0.42    inference(subsumption_resolution,[],[f227,f14])).
% 0.18/0.42  fof(f14,plain,(
% 0.18/0.42    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.18/0.42    inference(cnf_transformation,[],[f10])).
% 0.18/0.43  fof(f227,plain,(
% 0.18/0.43    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,sK3)),
% 0.18/0.43    inference(resolution,[],[f24,f17])).
% 0.18/0.43  fof(f17,plain,(
% 0.18/0.43    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.18/0.43    inference(cnf_transformation,[],[f10])).
% 0.18/0.43  fof(f24,plain,(
% 0.18/0.43    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_xboole_0(X1,X2)) )),
% 0.18/0.43    inference(cnf_transformation,[],[f13])).
% 0.18/0.43  fof(f13,plain,(
% 0.18/0.43    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.43    inference(ennf_transformation,[],[f6])).
% 0.18/0.43  fof(f6,axiom,(
% 0.18/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.18/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.18/0.43  % SZS output end Proof for theBenchmark
% 0.18/0.43  % (30593)------------------------------
% 0.18/0.43  % (30593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.43  % (30593)Termination reason: Refutation
% 0.18/0.43  
% 0.18/0.43  % (30593)Memory used [KB]: 10618
% 0.18/0.43  % (30593)Time elapsed: 0.014 s
% 0.18/0.43  % (30593)------------------------------
% 0.18/0.43  % (30593)------------------------------
% 0.18/0.43  % (30592)Success in time 0.096 s
%------------------------------------------------------------------------------
