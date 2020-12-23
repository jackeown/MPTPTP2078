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
% DateTime   : Thu Dec  3 12:45:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 217 expanded)
%              Number of leaves         :    9 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  147 ( 686 expanded)
%              Number of equality atoms :   22 (  65 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1498,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1495,f197])).

fof(f197,plain,(
    ~ r1_tarski(sK1,k4_xboole_0(sK0,sK3)) ),
    inference(backward_demodulation,[],[f30,f192])).

fof(f192,plain,(
    k3_subset_1(sK0,sK3) = k4_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f30,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1495,plain,(
    r1_tarski(sK1,k4_xboole_0(sK0,sK3)) ),
    inference(resolution,[],[f1491,f288])).

fof(f288,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | r1_tarski(sK1,k4_xboole_0(sK0,X0)) ) ),
    inference(resolution,[],[f287,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

% (22113)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f287,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f263,f28])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f263,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f48,f228])).

fof(f228,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f225,f218])).

fof(f218,plain,(
    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f212,f193])).

fof(f193,plain,(
    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f212,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f225,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f209,f39])).

fof(f209,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f207,f31])).

fof(f207,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f38,f193])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1491,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f1486,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1486,plain,(
    ! [X16] :
      ( ~ r1_tarski(X16,sK1)
      | r1_xboole_0(X16,sK3) ) ),
    inference(resolution,[],[f420,f988])).

fof(f988,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f978])).

fof(f978,plain,
    ( sK1 != sK1
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f43,f972])).

fof(f972,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f391,f28])).

fof(f391,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k4_xboole_0(X0,k4_xboole_0(sK0,sK2)) = X0 ) ),
    inference(resolution,[],[f264,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f264,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,k4_xboole_0(sK0,sK2))
      | ~ r1_tarski(X1,sK2) ) ),
    inference(superposition,[],[f49,f228])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f420,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(sK0,sK2))
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,sK3) ) ),
    inference(resolution,[],[f407,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f407,plain,(
    r1_tarski(sK3,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f281,f29])).

fof(f29,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f281,plain,(
    ! [X20] :
      ( ~ r1_xboole_0(sK3,X20)
      | r1_tarski(sK3,k4_xboole_0(sK0,X20)) ) ),
    inference(resolution,[],[f50,f248])).

fof(f248,plain,(
    r1_tarski(sK3,sK0) ),
    inference(superposition,[],[f65,f220])).

fof(f220,plain,(
    sK3 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) ),
    inference(backward_demodulation,[],[f204,f219])).

fof(f219,plain,(
    sK3 = k3_subset_1(sK0,k4_xboole_0(sK0,sK3)) ),
    inference(forward_demodulation,[],[f213,f192])).

fof(f213,plain,(
    sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3)) ),
    inference(resolution,[],[f40,f27])).

fof(f204,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK3)) ),
    inference(resolution,[],[f202,f39])).

% (22110)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f202,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK3),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f200,f27])).

fof(f200,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f38,f192])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f48,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:27:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (22131)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (22114)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.50  % (22131)Refutation not found, incomplete strategy% (22131)------------------------------
% 0.22/0.50  % (22131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22131)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22131)Memory used [KB]: 10746
% 0.22/0.50  % (22131)Time elapsed: 0.006 s
% 0.22/0.50  % (22131)------------------------------
% 0.22/0.50  % (22131)------------------------------
% 0.22/0.51  % (22111)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (22120)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (22118)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (22109)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (22136)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (22112)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (22108)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (22114)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (22127)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f1498,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f1495,f197])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ~r1_tarski(sK1,k4_xboole_0(sK0,sK3))),
% 0.22/0.53    inference(backward_demodulation,[],[f30,f192])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    k3_subset_1(sK0,sK3) = k4_xboole_0(sK0,sK3)),
% 0.22/0.53    inference(resolution,[],[f39,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f1495,plain,(
% 0.22/0.53    r1_tarski(sK1,k4_xboole_0(sK0,sK3))),
% 0.22/0.53    inference(resolution,[],[f1491,f288])).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_tarski(sK1,k4_xboole_0(sK0,X0))) )),
% 0.22/0.53    inference(resolution,[],[f287,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.22/0.53  % (22113)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  fof(f287,plain,(
% 0.22/0.53    r1_tarski(sK1,sK0)),
% 0.22/0.53    inference(resolution,[],[f263,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    r1_tarski(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK0)) )),
% 0.22/0.53    inference(superposition,[],[f48,f228])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f225,f218])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(forward_demodulation,[],[f212,f193])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK2) = k3_subset_1(sK0,sK2)),
% 0.22/0.53    inference(resolution,[],[f39,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.22/0.53    inference(resolution,[],[f40,f31])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.53    inference(resolution,[],[f209,f39])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f207,f31])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(superposition,[],[f38,f193])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.54  fof(f1491,plain,(
% 0.22/0.54    r1_xboole_0(sK1,sK3)),
% 0.22/0.54    inference(resolution,[],[f1486,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f47,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f1486,plain,(
% 0.22/0.54    ( ! [X16] : (~r1_tarski(X16,sK1) | r1_xboole_0(X16,sK3)) )),
% 0.22/0.54    inference(resolution,[],[f420,f988])).
% 0.22/0.54  fof(f988,plain,(
% 0.22/0.54    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f978])).
% 0.22/0.54  fof(f978,plain,(
% 0.22/0.54    sK1 != sK1 | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.54    inference(superposition,[],[f43,f972])).
% 0.22/0.54  fof(f972,plain,(
% 0.22/0.54    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.54    inference(resolution,[],[f391,f28])).
% 0.22/0.54  fof(f391,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK2) | k4_xboole_0(X0,k4_xboole_0(sK0,sK2)) = X0) )),
% 0.22/0.54    inference(resolution,[],[f264,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    ( ! [X1] : (r1_xboole_0(X1,k4_xboole_0(sK0,sK2)) | ~r1_tarski(X1,sK2)) )),
% 0.22/0.54    inference(superposition,[],[f49,f228])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f420,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_xboole_0(X1,k4_xboole_0(sK0,sK2)) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,sK3)) )),
% 0.22/0.54    inference(resolution,[],[f407,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.22/0.54  fof(f407,plain,(
% 0.22/0.54    r1_tarski(sK3,k4_xboole_0(sK0,sK2))),
% 0.22/0.54    inference(resolution,[],[f281,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    r1_xboole_0(sK3,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    ( ! [X20] : (~r1_xboole_0(sK3,X20) | r1_tarski(sK3,k4_xboole_0(sK0,X20))) )),
% 0.22/0.54    inference(resolution,[],[f50,f248])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    r1_tarski(sK3,sK0)),
% 0.22/0.54    inference(superposition,[],[f65,f220])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    sK3 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3))),
% 0.22/0.54    inference(backward_demodulation,[],[f204,f219])).
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    sK3 = k3_subset_1(sK0,k4_xboole_0(sK0,sK3))),
% 0.22/0.54    inference(forward_demodulation,[],[f213,f192])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    sK3 = k3_subset_1(sK0,k3_subset_1(sK0,sK3))),
% 0.22/0.54    inference(resolution,[],[f40,f27])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK3))),
% 0.22/0.54    inference(resolution,[],[f202,f39])).
% 0.22/0.54  % (22110)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    m1_subset_1(k4_xboole_0(sK0,sK3),k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f200,f27])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    m1_subset_1(k4_xboole_0(sK0,sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(superposition,[],[f38,f192])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.54    inference(resolution,[],[f48,f64])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (22114)------------------------------
% 0.22/0.54  % (22114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22114)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (22114)Memory used [KB]: 7036
% 0.22/0.54  % (22114)Time elapsed: 0.039 s
% 0.22/0.54  % (22114)------------------------------
% 0.22/0.54  % (22114)------------------------------
% 0.22/0.54  % (22103)Success in time 0.178 s
%------------------------------------------------------------------------------
