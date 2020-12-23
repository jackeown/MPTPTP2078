%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 224 expanded)
%              Number of leaves         :   11 (  54 expanded)
%              Depth                    :   20
%              Number of atoms          :  186 ( 753 expanded)
%              Number of equality atoms :  106 ( 403 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(subsumption_resolution,[],[f345,f89])).

fof(f89,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f88,f81])).

fof(f81,plain,(
    ! [X3] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X3 ) ),
    inference(superposition,[],[f32,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f65,f34])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK3(X0))
      | k1_xboole_0 = sK3(X0) ) ),
    inference(resolution,[],[f25,f32])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f32,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f87,f80])).

fof(f80,plain,(
    ! [X2] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != X2 ) ),
    inference(superposition,[],[f33,f77])).

fof(f33,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f86,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f86,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f85,f24])).

% (26221)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (26224)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (26204)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (26204)Refutation not found, incomplete strategy% (26204)------------------------------
% (26204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26204)Termination reason: Refutation not found, incomplete strategy

% (26204)Memory used [KB]: 10618
% (26204)Time elapsed: 0.149 s
% (26204)------------------------------
% (26204)------------------------------
% (26203)Refutation not found, incomplete strategy% (26203)------------------------------
% (26203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26203)Termination reason: Refutation not found, incomplete strategy

% (26203)Memory used [KB]: 10746
% (26203)Time elapsed: 0.153 s
% (26203)------------------------------
% (26203)------------------------------
% (26215)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f85,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f345,plain,(
    k1_xboole_0 = sK1 ),
    inference(equality_resolution,[],[f344])).

fof(f344,plain,(
    ! [X16] :
      ( sK1 != X16
      | k1_xboole_0 = X16 ) ),
    inference(global_subsumption,[],[f21,f89,f338])).

fof(f338,plain,(
    ! [X16] :
      ( k1_xboole_0 = sK0
      | sK1 != X16
      | k1_xboole_0 = X16 ) ),
    inference(resolution,[],[f320,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK1 != X0
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f140,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f140,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f138,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f92,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f90,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | ~ v1_funct_1(sK2(X0,X1))
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f138,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f38,f136])).

fof(f136,plain,(
    ! [X0] : sK4(k1_tarski(X0),sK0) = X0 ),
    inference(subsumption_resolution,[],[f135,f89])).

fof(f135,plain,(
    ! [X0] :
      ( sK4(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f96,f29])).

fof(f96,plain,(
    ! [X2,X3] :
      ( sK1 != k1_relat_1(sK2(X3,X2))
      | sK4(k1_tarski(X2),sK0) = X2
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f62,f93])).

fof(f62,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_tarski(X1),X2)
      | sK4(k1_tarski(X1),X2) = X1 ) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f320,plain,(
    ! [X7] :
      ( r2_hidden(sK6(k1_xboole_0,X7),X7)
      | k1_xboole_0 = X7 ) ),
    inference(forward_demodulation,[],[f305,f22])).

fof(f305,plain,(
    ! [X7] :
      ( r2_hidden(sK6(k1_xboole_0,X7),X7)
      | k1_relat_1(k1_xboole_0) = X7 ) ),
    inference(resolution,[],[f45,f58])).

fof(f58,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f35,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (26216)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (26209)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (26200)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (26196)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (26198)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (26195)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (26195)Refutation not found, incomplete strategy% (26195)------------------------------
% 0.20/0.52  % (26195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26195)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26195)Memory used [KB]: 1663
% 0.20/0.52  % (26195)Time elapsed: 0.107 s
% 0.20/0.52  % (26195)------------------------------
% 0.20/0.52  % (26195)------------------------------
% 0.20/0.52  % (26205)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (26201)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (26205)Refutation not found, incomplete strategy% (26205)------------------------------
% 0.20/0.52  % (26205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26205)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26205)Memory used [KB]: 10618
% 0.20/0.52  % (26205)Time elapsed: 0.109 s
% 0.20/0.52  % (26205)------------------------------
% 0.20/0.52  % (26205)------------------------------
% 0.20/0.52  % (26223)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (26206)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (26199)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (26213)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (26214)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (26203)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (26217)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (26217)Refutation not found, incomplete strategy% (26217)------------------------------
% 0.20/0.54  % (26217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26217)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26217)Memory used [KB]: 10746
% 0.20/0.54  % (26217)Time elapsed: 0.130 s
% 0.20/0.54  % (26217)------------------------------
% 0.20/0.54  % (26217)------------------------------
% 0.20/0.54  % (26220)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (26210)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (26208)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (26218)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (26202)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (26197)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (26211)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (26201)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f346,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f345,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    k1_xboole_0 != sK1),
% 0.20/0.55    inference(subsumption_resolution,[],[f88,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X3] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X3) )),
% 0.20/0.55    inference(superposition,[],[f32,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = sK3(X0) | k1_xboole_0 != X0) )),
% 0.20/0.55    inference(superposition,[],[f65,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | k1_xboole_0 = sK3(X0)) )),
% 0.20/0.55    inference(resolution,[],[f25,f32])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f87,f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2] : (v1_funct_1(k1_xboole_0) | k1_xboole_0 != X2) )),
% 0.20/0.55    inference(superposition,[],[f33,f77])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(forward_demodulation,[],[f86,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f85,f24])).
% 0.20/0.55  % (26221)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (26224)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.55  % (26204)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (26204)Refutation not found, incomplete strategy% (26204)------------------------------
% 1.50/0.56  % (26204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (26204)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (26204)Memory used [KB]: 10618
% 1.50/0.56  % (26204)Time elapsed: 0.149 s
% 1.50/0.56  % (26204)------------------------------
% 1.50/0.56  % (26204)------------------------------
% 1.50/0.56  % (26203)Refutation not found, incomplete strategy% (26203)------------------------------
% 1.50/0.56  % (26203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (26203)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (26203)Memory used [KB]: 10746
% 1.50/0.56  % (26203)Time elapsed: 0.153 s
% 1.50/0.56  % (26203)------------------------------
% 1.50/0.56  % (26203)------------------------------
% 1.50/0.56  % (26215)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.50/0.56  fof(f85,plain,(
% 1.50/0.56    ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.50/0.56    inference(superposition,[],[f20,f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.50/0.56    inference(cnf_transformation,[],[f7])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  fof(f14,plain,(
% 1.50/0.56    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.50/0.56    inference(flattening,[],[f13])).
% 1.50/0.56  fof(f13,plain,(
% 1.50/0.56    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.50/0.56    inference(negated_conjecture,[],[f11])).
% 1.50/0.56  fof(f11,conjecture,(
% 1.50/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.50/0.56  fof(f345,plain,(
% 1.50/0.56    k1_xboole_0 = sK1),
% 1.50/0.56    inference(equality_resolution,[],[f344])).
% 1.50/0.56  fof(f344,plain,(
% 1.50/0.56    ( ! [X16] : (sK1 != X16 | k1_xboole_0 = X16) )),
% 1.50/0.56    inference(global_subsumption,[],[f21,f89,f338])).
% 1.50/0.56  fof(f338,plain,(
% 1.50/0.56    ( ! [X16] : (k1_xboole_0 = sK0 | sK1 != X16 | k1_xboole_0 = X16) )),
% 1.50/0.56    inference(resolution,[],[f320,f144])).
% 1.50/0.56  fof(f144,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | sK1 != X0 | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f143])).
% 1.50/0.56  fof(f143,plain,(
% 1.50/0.56    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(superposition,[],[f140,f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.50/0.56  fof(f140,plain,(
% 1.50/0.56    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) )),
% 1.50/0.56    inference(resolution,[],[f138,f93])).
% 1.50/0.56  fof(f93,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f92,f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f92,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f90,f28])).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f90,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | ~v1_funct_1(sK2(X0,X1)) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(superposition,[],[f20,f30])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f138,plain,(
% 1.50/0.56    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) )),
% 1.50/0.56    inference(superposition,[],[f38,f136])).
% 1.50/0.56  fof(f136,plain,(
% 1.50/0.56    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f135,f89])).
% 1.50/0.56  fof(f135,plain,(
% 1.50/0.56    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = sK1) )),
% 1.50/0.56    inference(equality_resolution,[],[f134])).
% 1.50/0.56  fof(f134,plain,(
% 1.50/0.56    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f133])).
% 1.50/0.56  fof(f133,plain,(
% 1.50/0.56    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(superposition,[],[f96,f29])).
% 1.50/0.56  fof(f96,plain,(
% 1.50/0.56    ( ! [X2,X3] : (sK1 != k1_relat_1(sK2(X3,X2)) | sK4(k1_tarski(X2),sK0) = X2 | k1_xboole_0 = X3) )),
% 1.50/0.56    inference(resolution,[],[f62,f93])).
% 1.50/0.56  fof(f62,plain,(
% 1.50/0.56    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),X2) | sK4(k1_tarski(X1),X2) = X1) )),
% 1.50/0.56    inference(resolution,[],[f37,f50])).
% 1.50/0.56  fof(f50,plain,(
% 1.50/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.50/0.56    inference(equality_resolution,[],[f40])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.50/0.56  fof(f37,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f19])).
% 1.50/0.56  fof(f320,plain,(
% 1.50/0.56    ( ! [X7] : (r2_hidden(sK6(k1_xboole_0,X7),X7) | k1_xboole_0 = X7) )),
% 1.50/0.56    inference(forward_demodulation,[],[f305,f22])).
% 1.50/0.56  fof(f305,plain,(
% 1.50/0.56    ( ! [X7] : (r2_hidden(sK6(k1_xboole_0,X7),X7) | k1_relat_1(k1_xboole_0) = X7) )),
% 1.50/0.56    inference(resolution,[],[f45,f58])).
% 1.50/0.56  fof(f58,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.50/0.56    inference(superposition,[],[f35,f55])).
% 1.50/0.56  fof(f55,plain,(
% 1.50/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.56    inference(equality_resolution,[],[f49])).
% 1.50/0.56  fof(f49,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.50/0.56    inference(cnf_transformation,[],[f14])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (26201)------------------------------
% 1.50/0.56  % (26201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (26201)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (26201)Memory used [KB]: 6780
% 1.50/0.56  % (26201)Time elapsed: 0.121 s
% 1.50/0.56  % (26201)------------------------------
% 1.50/0.56  % (26201)------------------------------
% 1.50/0.56  % (26194)Success in time 0.198 s
%------------------------------------------------------------------------------
