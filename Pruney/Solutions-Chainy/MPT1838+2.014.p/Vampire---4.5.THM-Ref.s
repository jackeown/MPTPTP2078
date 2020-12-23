%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:56 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 110 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 320 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f198])).

fof(f198,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f196,f102])).

fof(f102,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f101,f77])).

fof(f77,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f33,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

% (14594)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f33,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f32,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f76,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f76,plain,(
    m1_subset_1(sK2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f32,f33,f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f196,plain,(
    ! [X0] : k1_tarski(X0) != sK1 ),
    inference(forward_demodulation,[],[f195,f87])).

fof(f87,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f34,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f195,plain,(
    ! [X0] : k1_tarski(X0) != k2_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f181,f35,f193,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f193,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f119,f53])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f119,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f118,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f118,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f44,f103,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f103,plain,(
    ~ r1_tarski(sK0,sK3(sK0)) ),
    inference(unit_resulting_resolution,[],[f78,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f78,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f36,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f35,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f181,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f112,f53])).

fof(f112,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f111,f42])).

fof(f111,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f44,f95,f39])).

fof(f95,plain,(
    ~ r1_tarski(sK1,sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f72,f62])).

fof(f72,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f32,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (14585)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (14579)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (14601)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.50  % (14587)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (14598)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (14593)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.51  % (14590)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (14603)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.51  % (14587)Refutation not found, incomplete strategy% (14587)------------------------------
% 0.19/0.51  % (14587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (14587)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (14587)Memory used [KB]: 10618
% 0.19/0.51  % (14587)Time elapsed: 0.095 s
% 0.19/0.51  % (14587)------------------------------
% 0.19/0.51  % (14587)------------------------------
% 0.19/0.51  % (14588)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (14598)Refutation not found, incomplete strategy% (14598)------------------------------
% 0.19/0.52  % (14598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (14598)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (14598)Memory used [KB]: 10746
% 0.19/0.52  % (14598)Time elapsed: 0.070 s
% 0.19/0.52  % (14598)------------------------------
% 0.19/0.52  % (14598)------------------------------
% 0.19/0.52  % (14593)Refutation not found, incomplete strategy% (14593)------------------------------
% 0.19/0.52  % (14593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (14581)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (14582)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (14605)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (14593)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (14593)Memory used [KB]: 10618
% 0.19/0.52  % (14593)Time elapsed: 0.116 s
% 0.19/0.52  % (14593)------------------------------
% 0.19/0.52  % (14593)------------------------------
% 0.19/0.52  % (14578)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (14577)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (14578)Refutation not found, incomplete strategy% (14578)------------------------------
% 0.19/0.52  % (14578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (14578)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (14578)Memory used [KB]: 10746
% 0.19/0.52  % (14578)Time elapsed: 0.117 s
% 0.19/0.52  % (14578)------------------------------
% 0.19/0.52  % (14578)------------------------------
% 0.19/0.52  % (14599)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.53  % (14597)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (14576)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (14602)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (14589)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (14580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (14604)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (14600)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.53  % (14580)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f199,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f198])).
% 0.19/0.53  fof(f198,plain,(
% 0.19/0.53    sK1 != sK1),
% 0.19/0.53    inference(superposition,[],[f196,f102])).
% 0.19/0.53  fof(f102,plain,(
% 0.19/0.53    sK1 = k1_tarski(sK2(sK1))),
% 0.19/0.53    inference(forward_demodulation,[],[f101,f77])).
% 0.19/0.53  fof(f77,plain,(
% 0.19/0.53    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f32,f33,f46])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f18])).
% 0.19/0.53  % (14594)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  fof(f18,axiom,(
% 0.19/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    v1_zfmisc_1(sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.53    inference(flattening,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.19/0.53    inference(ennf_transformation,[],[f20])).
% 0.19/0.53  fof(f20,negated_conjecture,(
% 0.19/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.19/0.53    inference(negated_conjecture,[],[f19])).
% 0.19/0.53  fof(f19,conjecture,(
% 0.19/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ~v1_xboole_0(sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f101,plain,(
% 0.19/0.53    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f32,f76,f48])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.53    inference(flattening,[],[f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,axiom,(
% 0.19/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.53  fof(f76,plain,(
% 0.19/0.53    m1_subset_1(sK2(sK1),sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f32,f33,f45])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f27])).
% 0.19/0.53  fof(f196,plain,(
% 0.19/0.53    ( ! [X0] : (k1_tarski(X0) != sK1) )),
% 0.19/0.53    inference(forward_demodulation,[],[f195,f87])).
% 0.19/0.53  fof(f87,plain,(
% 0.19/0.53    sK1 = k2_xboole_0(sK0,sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f34,f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.53  fof(f34,plain,(
% 0.19/0.53    r1_tarski(sK0,sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f195,plain,(
% 0.19/0.53    ( ! [X0] : (k1_tarski(X0) != k2_xboole_0(sK0,sK1)) )),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f181,f35,f193,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.19/0.53    inference(cnf_transformation,[],[f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.19/0.53    inference(ennf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.19/0.53  fof(f193,plain,(
% 0.19/0.53    k1_xboole_0 != sK0),
% 0.19/0.53    inference(superposition,[],[f119,f53])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,axiom,(
% 0.19/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.53  fof(f119,plain,(
% 0.19/0.53    k1_xboole_0 != k4_xboole_0(sK0,k1_xboole_0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f118,f42])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.53  fof(f118,plain,(
% 0.19/0.53    ~r1_tarski(sK0,k1_xboole_0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f103,f39])).
% 0.19/0.53  fof(f39,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(flattening,[],[f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.53  fof(f103,plain,(
% 0.19/0.53    ~r1_tarski(sK0,sK3(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f78,f62])).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f31])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,axiom,(
% 0.19/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.53  fof(f78,plain,(
% 0.19/0.53    r2_hidden(sK3(sK0),sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f36,f49])).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ~v1_xboole_0(sK0)),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    sK0 != sK1),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f181,plain,(
% 0.19/0.53    k1_xboole_0 != sK1),
% 0.19/0.53    inference(superposition,[],[f112,f53])).
% 0.19/0.53  fof(f112,plain,(
% 0.19/0.53    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f111,f42])).
% 0.19/0.53  fof(f111,plain,(
% 0.19/0.53    ~r1_tarski(sK1,k1_xboole_0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f95,f39])).
% 0.19/0.53  fof(f95,plain,(
% 0.19/0.53    ~r1_tarski(sK1,sK3(sK1))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f72,f62])).
% 0.19/0.53  fof(f72,plain,(
% 0.19/0.53    r2_hidden(sK3(sK1),sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f32,f49])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (14580)------------------------------
% 0.19/0.53  % (14580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (14580)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (14580)Memory used [KB]: 6268
% 0.19/0.53  % (14580)Time elapsed: 0.131 s
% 0.19/0.53  % (14580)------------------------------
% 0.19/0.53  % (14580)------------------------------
% 0.19/0.53  % (14575)Success in time 0.178 s
%------------------------------------------------------------------------------
