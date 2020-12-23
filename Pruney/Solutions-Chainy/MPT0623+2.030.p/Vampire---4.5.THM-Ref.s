%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:06 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 177 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   20
%              Number of atoms          :  178 ( 624 expanded)
%              Number of equality atoms :  102 ( 321 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(equality_resolution,[],[f329])).

fof(f329,plain,(
    ! [X16] : sK1 != X16 ),
    inference(global_subsumption,[],[f20,f89,f324])).

fof(f324,plain,(
    ! [X16] :
      ( k1_xboole_0 = sK0
      | sK1 != X16 ) ),
    inference(resolution,[],[f304,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f147,f88])).

fof(f88,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f87,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f87,plain,(
    ! [X1] :
      ( sK1 != k1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f86,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X1] :
      ( sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f85,f32])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3(X1))
      | sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f82,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f82,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | ~ v1_funct_1(sK3(X1))
      | sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f19,f80])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f78,f33])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != k1_relat_1(sK3(X0)) ) ),
    inference(resolution,[],[f25,f31])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f147,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f143,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f143,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f141,f98])).

fof(f98,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f97,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f95,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | ~ v1_funct_1(sK2(X2,X3))
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f19,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f141,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f37,f139])).

fof(f139,plain,(
    ! [X0] : sK4(k1_tarski(X0),sK0) = X0 ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1 ) ),
    inference(subsumption_resolution,[],[f137,f88])).

fof(f137,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f102,f28])).

fof(f102,plain,(
    ! [X2,X3] :
      ( sK1 != k1_relat_1(sK2(X3,X2))
      | sK4(k1_tarski(X2),sK0) = X2
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f61,f98])).

fof(f61,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_tarski(X1),X2)
      | sK4(k1_tarski(X1),X2) = X1 ) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f304,plain,(
    ! [X7] :
      ( r2_hidden(sK6(k1_xboole_0,X7),X7)
      | k1_xboole_0 = X7 ) ),
    inference(forward_demodulation,[],[f287,f21])).

fof(f21,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f287,plain,(
    ! [X7] :
      ( r2_hidden(sK6(k1_xboole_0,X7),X7)
      | k1_relat_1(k1_xboole_0) = X7 ) ),
    inference(resolution,[],[f44,f57])).

fof(f57,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f34,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f89,plain,(
    k1_xboole_0 != sK1 ),
    inference(equality_resolution,[],[f88])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:51:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (28836)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28836)Refutation not found, incomplete strategy% (28836)------------------------------
% 0.21/0.51  % (28836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28844)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (28836)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28836)Memory used [KB]: 10746
% 0.21/0.52  % (28836)Time elapsed: 0.105 s
% 0.21/0.52  % (28836)------------------------------
% 0.21/0.52  % (28836)------------------------------
% 0.21/0.52  % (28844)Refutation not found, incomplete strategy% (28844)------------------------------
% 0.21/0.52  % (28844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28844)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28844)Memory used [KB]: 10618
% 0.21/0.52  % (28844)Time elapsed: 0.107 s
% 0.21/0.52  % (28844)------------------------------
% 0.21/0.52  % (28844)------------------------------
% 0.21/0.52  % (28846)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (28851)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (28838)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (28851)Refutation not found, incomplete strategy% (28851)------------------------------
% 0.21/0.52  % (28851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28851)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28851)Memory used [KB]: 10618
% 0.21/0.52  % (28851)Time elapsed: 0.111 s
% 0.21/0.52  % (28851)------------------------------
% 0.21/0.52  % (28851)------------------------------
% 0.21/0.53  % (28840)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (28835)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28837)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (28839)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (28863)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (28858)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (28855)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (28838)Refutation not found, incomplete strategy% (28838)------------------------------
% 0.21/0.54  % (28838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28860)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (28834)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (28859)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (28845)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (28843)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (28843)Refutation not found, incomplete strategy% (28843)------------------------------
% 0.21/0.55  % (28843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28843)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28843)Memory used [KB]: 10618
% 0.21/0.55  % (28843)Time elapsed: 0.140 s
% 0.21/0.55  % (28843)------------------------------
% 0.21/0.55  % (28843)------------------------------
% 0.21/0.55  % (28853)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (28852)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (28861)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (28847)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (28849)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (28862)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (28854)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (28850)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.57  % (28857)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.57  % (28834)Refutation not found, incomplete strategy% (28834)------------------------------
% 1.54/0.57  % (28834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (28834)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (28834)Memory used [KB]: 1663
% 1.54/0.57  % (28834)Time elapsed: 0.149 s
% 1.54/0.57  % (28834)------------------------------
% 1.54/0.57  % (28834)------------------------------
% 1.54/0.57  % (28842)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.54/0.57  % (28842)Refutation not found, incomplete strategy% (28842)------------------------------
% 1.54/0.57  % (28842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (28842)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (28842)Memory used [KB]: 10746
% 1.54/0.57  % (28842)Time elapsed: 0.165 s
% 1.54/0.57  % (28842)------------------------------
% 1.54/0.57  % (28842)------------------------------
% 1.54/0.57  % (28838)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (28838)Memory used [KB]: 6396
% 1.54/0.57  % (28838)Time elapsed: 0.133 s
% 1.54/0.57  % (28838)------------------------------
% 1.54/0.57  % (28838)------------------------------
% 1.54/0.57  % (28840)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  fof(f330,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(equality_resolution,[],[f329])).
% 1.54/0.57  fof(f329,plain,(
% 1.54/0.57    ( ! [X16] : (sK1 != X16) )),
% 1.54/0.57    inference(global_subsumption,[],[f20,f89,f324])).
% 1.54/0.57  fof(f324,plain,(
% 1.54/0.57    ( ! [X16] : (k1_xboole_0 = sK0 | sK1 != X16) )),
% 1.54/0.57    inference(resolution,[],[f304,f148])).
% 1.54/0.57  fof(f148,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | sK1 != X0) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f147,f88])).
% 1.54/0.57  fof(f88,plain,(
% 1.54/0.57    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) )),
% 1.54/0.57    inference(superposition,[],[f87,f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f17])).
% 1.54/0.57  fof(f17,plain,(
% 1.54/0.57    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.54/0.57    inference(ennf_transformation,[],[f9])).
% 1.54/0.57  fof(f9,axiom,(
% 1.54/0.57    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.54/0.57  fof(f87,plain,(
% 1.54/0.57    ( ! [X1] : (sK1 != k1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f86,f31])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f17])).
% 1.54/0.57  fof(f86,plain,(
% 1.54/0.57    ( ! [X1] : (sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f85,f32])).
% 1.54/0.57  fof(f32,plain,(
% 1.54/0.57    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f17])).
% 1.54/0.57  fof(f85,plain,(
% 1.54/0.57    ( ! [X1] : (~v1_funct_1(sK3(X1)) | sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f82,f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.54/0.57  fof(f82,plain,(
% 1.54/0.57    ( ! [X1] : (~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(sK3(X1)) | sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.54/0.57    inference(superposition,[],[f19,f80])).
% 1.54/0.57  fof(f80,plain,(
% 1.54/0.57    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 1.54/0.57    inference(forward_demodulation,[],[f78,f33])).
% 1.54/0.57  fof(f78,plain,(
% 1.54/0.57    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != k1_relat_1(sK3(X0))) )),
% 1.54/0.57    inference(resolution,[],[f25,f31])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f15])).
% 1.54/0.57  fof(f15,plain,(
% 1.54/0.57    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.54/0.57  fof(f19,plain,(
% 1.54/0.57    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,plain,(
% 1.54/0.57    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.54/0.57    inference(flattening,[],[f13])).
% 1.54/0.57  fof(f13,plain,(
% 1.54/0.57    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f12])).
% 1.54/0.57  fof(f12,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.54/0.57    inference(negated_conjecture,[],[f11])).
% 1.54/0.57  fof(f11,conjecture,(
% 1.54/0.57    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.54/0.57  fof(f147,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f146])).
% 1.54/0.57  fof(f146,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(superposition,[],[f143,f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.54/0.57    inference(ennf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.54/0.57  fof(f143,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) )),
% 1.54/0.57    inference(resolution,[],[f141,f98])).
% 1.54/0.57  fof(f98,plain,(
% 1.54/0.57    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f97,f26])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f16])).
% 1.54/0.57  fof(f97,plain,(
% 1.54/0.57    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f95,f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f16])).
% 1.54/0.57  fof(f95,plain,(
% 1.54/0.57    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | ~v1_funct_1(sK2(X2,X3)) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.54/0.57    inference(superposition,[],[f19,f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f16])).
% 1.54/0.57  fof(f141,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) )),
% 1.54/0.57    inference(superposition,[],[f37,f139])).
% 1.54/0.57  fof(f139,plain,(
% 1.54/0.57    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0) )),
% 1.54/0.57    inference(equality_resolution,[],[f138])).
% 1.54/0.57  fof(f138,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f137,f88])).
% 1.54/0.57  fof(f137,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(duplicate_literal_removal,[],[f136])).
% 1.54/0.57  fof(f136,plain,(
% 1.54/0.57    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(superposition,[],[f102,f28])).
% 1.54/0.57  fof(f102,plain,(
% 1.54/0.57    ( ! [X2,X3] : (sK1 != k1_relat_1(sK2(X3,X2)) | sK4(k1_tarski(X2),sK0) = X2 | k1_xboole_0 = X3) )),
% 1.54/0.57    inference(resolution,[],[f61,f98])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),X2) | sK4(k1_tarski(X1),X2) = X1) )),
% 1.54/0.57    inference(resolution,[],[f36,f49])).
% 1.54/0.57  fof(f49,plain,(
% 1.54/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.54/0.57    inference(equality_resolution,[],[f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f3])).
% 1.54/0.57  fof(f3,axiom,(
% 1.54/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f18])).
% 1.54/0.57  fof(f18,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f18])).
% 1.54/0.57  fof(f304,plain,(
% 1.54/0.57    ( ! [X7] : (r2_hidden(sK6(k1_xboole_0,X7),X7) | k1_xboole_0 = X7) )),
% 1.54/0.57    inference(forward_demodulation,[],[f287,f21])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.54/0.57    inference(cnf_transformation,[],[f7])).
% 1.54/0.57  fof(f7,axiom,(
% 1.54/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.54/0.57  fof(f287,plain,(
% 1.54/0.57    ( ! [X7] : (r2_hidden(sK6(k1_xboole_0,X7),X7) | k1_relat_1(k1_xboole_0) = X7) )),
% 1.54/0.57    inference(resolution,[],[f44,f57])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.54/0.57    inference(superposition,[],[f34,f54])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.54/0.57    inference(equality_resolution,[],[f48])).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f4])).
% 1.54/0.57  fof(f4,axiom,(
% 1.54/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f5])).
% 1.54/0.57  fof(f5,axiom,(
% 1.54/0.57    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.54/0.57  fof(f44,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.54/0.57  fof(f89,plain,(
% 1.54/0.57    k1_xboole_0 != sK1),
% 1.54/0.57    inference(equality_resolution,[],[f88])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.54/0.57    inference(cnf_transformation,[],[f14])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (28840)------------------------------
% 1.54/0.57  % (28840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (28840)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (28840)Memory used [KB]: 6780
% 1.54/0.57  % (28840)Time elapsed: 0.168 s
% 1.54/0.57  % (28840)------------------------------
% 1.54/0.57  % (28840)------------------------------
% 1.54/0.57  % (28833)Success in time 0.202 s
%------------------------------------------------------------------------------
