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
% DateTime   : Thu Dec  3 13:20:00 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 150 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  152 ( 431 expanded)
%              Number of equality atoms :   73 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f42,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f91,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f30,f88])).

fof(f88,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f86,f76])).

fof(f76,plain,(
    sK1 = k2_tarski(sK2(sK1),sK2(sK1)) ),
    inference(forward_demodulation,[],[f75,f65])).

fof(f65,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f64,f26])).

fof(f26,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f64,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f75,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) ),
    inference(subsumption_resolution,[],[f74,f26])).

fof(f74,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f73,f27])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f41,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f86,plain,(
    ! [X2] :
      ( sK1 != k2_tarski(X2,X2)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f85,f77])).

% (478)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f60,f76])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 != k2_tarski(X0,X0) ),
    inference(superposition,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

% (454)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (463)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (476)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f47,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)) ),
    inference(definition_unfolding,[],[f37,f38,f33])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f85,plain,(
    ! [X2] :
      ( sK1 != k2_tarski(X2,X2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f83,f29])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    ! [X2] :
      ( sK1 != k2_tarski(X2,X2)
      | sK0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f50,f61])).

fof(f61,plain,(
    sK1 = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) != k3_tarski(k2_tarski(X1,X2))
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(definition_unfolding,[],[f45,f33,f38])).

% (469)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (468)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (458)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (470)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (454)Refutation not found, incomplete strategy% (454)------------------------------
% (454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (469)Refutation not found, incomplete strategy% (469)------------------------------
% (469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (469)Termination reason: Refutation not found, incomplete strategy

% (469)Memory used [KB]: 6140
% (469)Time elapsed: 0.128 s
% (469)------------------------------
% (469)------------------------------
% (454)Termination reason: Refutation not found, incomplete strategy

% (454)Memory used [KB]: 1791
% (454)Time elapsed: 0.127 s
% (454)------------------------------
% (454)------------------------------
fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f30,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (455)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (464)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (464)Refutation not found, incomplete strategy% (464)------------------------------
% 0.21/0.51  % (464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (464)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (464)Memory used [KB]: 10618
% 0.21/0.51  % (464)Time elapsed: 0.104 s
% 0.21/0.51  % (464)------------------------------
% 0.21/0.51  % (464)------------------------------
% 0.21/0.51  % (456)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (456)Refutation not found, incomplete strategy% (456)------------------------------
% 1.21/0.52  % (456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (456)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (456)Memory used [KB]: 10746
% 1.21/0.52  % (456)Time elapsed: 0.110 s
% 1.21/0.52  % (456)------------------------------
% 1.21/0.52  % (456)------------------------------
% 1.21/0.52  % (460)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.52  % (472)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.21/0.52  % (461)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.52  % (462)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.53  % (460)Refutation found. Thanks to Tanya!
% 1.21/0.53  % SZS status Theorem for theBenchmark
% 1.21/0.53  % SZS output start Proof for theBenchmark
% 1.21/0.53  fof(f96,plain,(
% 1.21/0.53    $false),
% 1.21/0.53    inference(subsumption_resolution,[],[f91,f58])).
% 1.21/0.53  fof(f58,plain,(
% 1.21/0.53    v1_xboole_0(k1_xboole_0)),
% 1.21/0.53    inference(subsumption_resolution,[],[f57,f31])).
% 1.21/0.53  fof(f31,plain,(
% 1.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f4])).
% 1.21/0.53  fof(f4,axiom,(
% 1.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.21/0.53  fof(f57,plain,(
% 1.21/0.53    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_xboole_0(k1_xboole_0)) )),
% 1.21/0.53    inference(resolution,[],[f56,f39])).
% 1.21/0.53  fof(f39,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.21/0.53    inference(flattening,[],[f19])).
% 1.21/0.53  fof(f19,plain,(
% 1.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f5])).
% 1.21/0.53  fof(f5,axiom,(
% 1.21/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.21/0.53  fof(f56,plain,(
% 1.21/0.53    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(trivial_inequality_removal,[],[f55])).
% 1.21/0.53  fof(f55,plain,(
% 1.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(superposition,[],[f42,f52])).
% 1.21/0.53  fof(f52,plain,(
% 1.21/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.21/0.53    inference(resolution,[],[f43,f31])).
% 1.21/0.53  fof(f43,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.21/0.53    inference(cnf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.21/0.53  fof(f42,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f24])).
% 1.21/0.53  fof(f24,plain,(
% 1.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 1.21/0.53    inference(ennf_transformation,[],[f15])).
% 1.21/0.53  fof(f15,plain,(
% 1.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 1.21/0.53    inference(unused_predicate_definition_removal,[],[f6])).
% 1.21/0.53  fof(f6,axiom,(
% 1.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.21/0.53  fof(f91,plain,(
% 1.21/0.53    ~v1_xboole_0(k1_xboole_0)),
% 1.21/0.53    inference(backward_demodulation,[],[f30,f88])).
% 1.21/0.53  fof(f88,plain,(
% 1.21/0.53    k1_xboole_0 = sK0),
% 1.21/0.53    inference(trivial_inequality_removal,[],[f87])).
% 1.21/0.53  fof(f87,plain,(
% 1.21/0.53    sK1 != sK1 | k1_xboole_0 = sK0),
% 1.21/0.53    inference(superposition,[],[f86,f76])).
% 1.21/0.53  fof(f76,plain,(
% 1.21/0.53    sK1 = k2_tarski(sK2(sK1),sK2(sK1))),
% 1.21/0.53    inference(forward_demodulation,[],[f75,f65])).
% 1.21/0.53  fof(f65,plain,(
% 1.21/0.53    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 1.21/0.53    inference(subsumption_resolution,[],[f64,f26])).
% 1.21/0.53  fof(f26,plain,(
% 1.21/0.53    ~v1_xboole_0(sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f17])).
% 1.21/0.53  fof(f17,plain,(
% 1.21/0.53    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.21/0.53    inference(flattening,[],[f16])).
% 1.21/0.53  fof(f16,plain,(
% 1.21/0.53    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.21/0.53    inference(ennf_transformation,[],[f14])).
% 1.21/0.53  fof(f14,negated_conjecture,(
% 1.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.21/0.53    inference(negated_conjecture,[],[f13])).
% 1.21/0.53  fof(f13,conjecture,(
% 1.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.21/0.53  fof(f64,plain,(
% 1.21/0.53    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 1.21/0.53    inference(resolution,[],[f35,f27])).
% 1.21/0.53  fof(f27,plain,(
% 1.21/0.53    v1_zfmisc_1(sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f17])).
% 1.21/0.53  fof(f35,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f18])).
% 1.21/0.53  fof(f18,plain,(
% 1.21/0.53    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.21/0.53    inference(ennf_transformation,[],[f12])).
% 1.21/0.53  fof(f12,axiom,(
% 1.21/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 1.21/0.53  fof(f75,plain,(
% 1.21/0.53    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1))),
% 1.21/0.53    inference(subsumption_resolution,[],[f74,f26])).
% 1.21/0.53  fof(f74,plain,(
% 1.21/0.53    k6_domain_1(sK1,sK2(sK1)) = k2_tarski(sK2(sK1),sK2(sK1)) | v1_xboole_0(sK1)),
% 1.21/0.53    inference(resolution,[],[f73,f27])).
% 1.21/0.53  fof(f73,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) | v1_xboole_0(X0)) )),
% 1.21/0.53    inference(duplicate_literal_removal,[],[f72])).
% 1.21/0.53  fof(f72,plain,(
% 1.21/0.53    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k2_tarski(sK2(X0),sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.21/0.53    inference(resolution,[],[f49,f34])).
% 1.21/0.53  fof(f34,plain,(
% 1.21/0.53    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f18])).
% 1.21/0.53  fof(f49,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 1.21/0.53    inference(definition_unfolding,[],[f41,f33])).
% 1.21/0.53  fof(f33,plain,(
% 1.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,axiom,(
% 1.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.21/0.53  fof(f41,plain,(
% 1.21/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f23])).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.21/0.53    inference(flattening,[],[f22])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.21/0.53    inference(ennf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,axiom,(
% 1.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.21/0.53  fof(f86,plain,(
% 1.21/0.53    ( ! [X2] : (sK1 != k2_tarski(X2,X2) | k1_xboole_0 = sK0) )),
% 1.21/0.53    inference(subsumption_resolution,[],[f85,f77])).
% 1.21/0.53  % (478)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.21/0.53  fof(f77,plain,(
% 1.21/0.53    k1_xboole_0 != sK1),
% 1.21/0.53    inference(superposition,[],[f60,f76])).
% 1.21/0.53  fof(f60,plain,(
% 1.21/0.53    ( ! [X0] : (k1_xboole_0 != k2_tarski(X0,X0)) )),
% 1.21/0.53    inference(superposition,[],[f47,f46])).
% 1.21/0.53  fof(f46,plain,(
% 1.21/0.53    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 1.21/0.53    inference(definition_unfolding,[],[f32,f38])).
% 1.21/0.53  fof(f38,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f8])).
% 1.21/0.53  fof(f8,axiom,(
% 1.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.21/0.53  fof(f32,plain,(
% 1.21/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.21/0.53    inference(cnf_transformation,[],[f3])).
% 1.21/0.53  % (454)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.53  % (463)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.21/0.53  % (476)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.21/0.53  fof(f47,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_tarski(k2_tarski(X0,X0),X1))) )),
% 1.21/0.53    inference(definition_unfolding,[],[f37,f38,f33])).
% 1.21/0.53  fof(f37,plain,(
% 1.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,axiom,(
% 1.21/0.53    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.21/0.53  fof(f85,plain,(
% 1.21/0.53    ( ! [X2] : (sK1 != k2_tarski(X2,X2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 1.21/0.53    inference(subsumption_resolution,[],[f83,f29])).
% 1.21/0.53  fof(f29,plain,(
% 1.21/0.53    sK0 != sK1),
% 1.21/0.53    inference(cnf_transformation,[],[f17])).
% 1.21/0.53  fof(f83,plain,(
% 1.21/0.53    ( ! [X2] : (sK1 != k2_tarski(X2,X2) | sK0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 1.21/0.53    inference(superposition,[],[f50,f61])).
% 1.21/0.53  fof(f61,plain,(
% 1.21/0.53    sK1 = k3_tarski(k2_tarski(sK0,sK1))),
% 1.21/0.53    inference(resolution,[],[f48,f28])).
% 1.21/0.53  fof(f28,plain,(
% 1.21/0.53    r1_tarski(sK0,sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f17])).
% 1.21/0.53  fof(f48,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 1.21/0.53    inference(definition_unfolding,[],[f40,f38])).
% 1.21/0.53  fof(f40,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f2])).
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.21/0.53  fof(f50,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) != k3_tarski(k2_tarski(X1,X2)) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.21/0.53    inference(definition_unfolding,[],[f45,f33,f38])).
% 1.21/0.53  % (469)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.53  % (468)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.53  % (458)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (470)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.54  % (454)Refutation not found, incomplete strategy% (454)------------------------------
% 1.34/0.54  % (454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (469)Refutation not found, incomplete strategy% (469)------------------------------
% 1.34/0.54  % (469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (469)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (469)Memory used [KB]: 6140
% 1.34/0.54  % (469)Time elapsed: 0.128 s
% 1.34/0.54  % (469)------------------------------
% 1.34/0.54  % (469)------------------------------
% 1.34/0.54  % (454)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (454)Memory used [KB]: 1791
% 1.34/0.54  % (454)Time elapsed: 0.127 s
% 1.34/0.54  % (454)------------------------------
% 1.34/0.54  % (454)------------------------------
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f25])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ~v1_xboole_0(sK0)),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (460)------------------------------
% 1.34/0.54  % (460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (460)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (460)Memory used [KB]: 6268
% 1.34/0.54  % (460)Time elapsed: 0.112 s
% 1.34/0.54  % (460)------------------------------
% 1.34/0.54  % (460)------------------------------
% 1.34/0.54  % (453)Success in time 0.178 s
%------------------------------------------------------------------------------
