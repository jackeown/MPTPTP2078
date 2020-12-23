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
% DateTime   : Thu Dec  3 12:52:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 454 expanded)
%              Number of leaves         :   13 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  156 (1326 expanded)
%              Number of equality atoms :   76 ( 688 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(global_subsumption,[],[f156,f815])).

% (2851)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f815,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f811,f24])).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f811,plain,(
    k1_relat_1(k1_xboole_0) = sK0 ),
    inference(unit_resulting_resolution,[],[f91,f792,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f792,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f347,f781])).

fof(f781,plain,(
    ! [X0] : sK3(k1_tarski(X0),sK0) = X0 ),
    inference(unit_resulting_resolution,[],[f344,f100])).

fof(f100,plain,(
    ! [X2,X1] :
      ( sK3(k1_tarski(X1),X2) = X1
      | r1_tarski(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
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

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f344,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),sK0) ),
    inference(forward_demodulation,[],[f338,f201])).

fof(f201,plain,(
    ! [X0] : k1_tarski(X0) = k2_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f155,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f155,plain,(
    k1_xboole_0 != sK1 ),
    inference(unit_resulting_resolution,[],[f146,f27,f149,f68])).

fof(f68,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f66,f25])).

fof(f25,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(superposition,[],[f22,f24])).

fof(f22,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f149,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f55,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = sK8(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f54,f56,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f56,plain,(
    ! [X0,X1] : k1_relat_1(sK8(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(sK8(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] : v1_funct_1(sK8(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f146,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f26,f133])).

fof(f133,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f28,f30])).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f338,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f157,f158,f165,f22])).

fof(f165,plain,(
    ! [X0] : sK1 = k1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f155,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f158,plain,(
    ! [X0] : v1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f155,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f157,plain,(
    ! [X0] : v1_funct_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f155,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f347,plain,(
    ! [X0] : ~ r2_hidden(sK3(k1_tarski(X0),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f344,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f91,plain,(
    ! [X0] : ~ sP6(X0,k1_xboole_0) ),
    inference(global_subsumption,[],[f64,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ sP6(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f61,f24])).

fof(f61,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f36,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
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

fof(f36,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f156,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f155,f23])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:55:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (2841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.48  % (2824)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (2824)Refutation not found, incomplete strategy% (2824)------------------------------
% 0.22/0.48  % (2824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2824)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (2824)Memory used [KB]: 10618
% 0.22/0.48  % (2824)Time elapsed: 0.074 s
% 0.22/0.48  % (2824)------------------------------
% 0.22/0.48  % (2824)------------------------------
% 0.22/0.51  % (2821)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (2820)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (2819)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (2816)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (2836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (2830)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (2837)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (2836)Refutation not found, incomplete strategy% (2836)------------------------------
% 0.22/0.52  % (2836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2836)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2836)Memory used [KB]: 10746
% 0.22/0.52  % (2836)Time elapsed: 0.106 s
% 0.22/0.52  % (2836)------------------------------
% 0.22/0.52  % (2836)------------------------------
% 0.22/0.53  % (2825)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (2840)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (2838)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (2842)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (2828)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (2835)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (2822)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (2822)Refutation not found, incomplete strategy% (2822)------------------------------
% 0.22/0.53  % (2822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2822)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2822)Memory used [KB]: 10746
% 0.22/0.53  % (2822)Time elapsed: 0.108 s
% 0.22/0.53  % (2822)------------------------------
% 0.22/0.53  % (2822)------------------------------
% 0.22/0.53  % (2839)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (2818)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (2833)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (2843)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (2815)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (2829)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (2832)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (2814)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (2817)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (2826)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (2831)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (2823)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (2827)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (2823)Refutation not found, incomplete strategy% (2823)------------------------------
% 0.22/0.55  % (2823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2831)Refutation not found, incomplete strategy% (2831)------------------------------
% 0.22/0.55  % (2831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2823)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2823)Memory used [KB]: 10618
% 0.22/0.55  % (2823)Time elapsed: 0.122 s
% 0.22/0.55  % (2823)------------------------------
% 0.22/0.55  % (2823)------------------------------
% 0.22/0.55  % (2816)Refutation not found, incomplete strategy% (2816)------------------------------
% 0.22/0.55  % (2816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2816)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2816)Memory used [KB]: 10746
% 0.22/0.55  % (2816)Time elapsed: 0.126 s
% 0.22/0.55  % (2816)------------------------------
% 0.22/0.55  % (2816)------------------------------
% 0.22/0.55  % (2831)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2831)Memory used [KB]: 10618
% 0.22/0.55  % (2831)Time elapsed: 0.129 s
% 0.22/0.55  % (2831)------------------------------
% 0.22/0.55  % (2831)------------------------------
% 0.22/0.55  % (2834)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (2838)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (2814)Refutation not found, incomplete strategy% (2814)------------------------------
% 0.22/0.56  % (2814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2814)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2814)Memory used [KB]: 1663
% 0.22/0.56  % (2814)Time elapsed: 0.128 s
% 0.22/0.56  % (2814)------------------------------
% 0.22/0.56  % (2814)------------------------------
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f816,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(global_subsumption,[],[f156,f815])).
% 1.59/0.59  % (2851)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.59/0.59  fof(f815,plain,(
% 1.59/0.59    k1_xboole_0 = sK0),
% 1.59/0.59    inference(forward_demodulation,[],[f811,f24])).
% 1.59/0.59  fof(f24,plain,(
% 1.59/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.59    inference(cnf_transformation,[],[f8])).
% 1.59/0.59  fof(f8,axiom,(
% 1.59/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.59/0.59  fof(f811,plain,(
% 1.59/0.59    k1_relat_1(k1_xboole_0) = sK0),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f91,f792,f48])).
% 1.59/0.59  fof(f48,plain,(
% 1.59/0.59    ( ! [X0,X1] : (sP6(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.59/0.59    inference(cnf_transformation,[],[f6])).
% 1.59/0.59  fof(f6,axiom,(
% 1.59/0.59    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.59/0.59  fof(f792,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.59/0.59    inference(backward_demodulation,[],[f347,f781])).
% 1.59/0.59  fof(f781,plain,(
% 1.59/0.59    ( ! [X0] : (sK3(k1_tarski(X0),sK0) = X0) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f344,f100])).
% 1.59/0.59  fof(f100,plain,(
% 1.59/0.59    ( ! [X2,X1] : (sK3(k1_tarski(X1),X2) = X1 | r1_tarski(k1_tarski(X1),X2)) )),
% 1.59/0.59    inference(resolution,[],[f38,f57])).
% 1.59/0.59  fof(f57,plain,(
% 1.59/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.59/0.59    inference(equality_resolution,[],[f41])).
% 1.59/0.59  fof(f41,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.59/0.59    inference(cnf_transformation,[],[f3])).
% 1.59/0.59  fof(f3,axiom,(
% 1.59/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.59/0.59  fof(f38,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f20])).
% 1.59/0.59  fof(f20,plain,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f1])).
% 1.59/0.59  fof(f1,axiom,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.59/0.59  fof(f344,plain,(
% 1.59/0.59    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0)) )),
% 1.59/0.59    inference(forward_demodulation,[],[f338,f201])).
% 1.59/0.59  fof(f201,plain,(
% 1.59/0.59    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK2(sK1,X0))) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f155,f35])).
% 1.59/0.59  fof(f35,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f19])).
% 1.59/0.59  fof(f19,plain,(
% 1.59/0.59    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.59/0.59    inference(ennf_transformation,[],[f12])).
% 1.59/0.59  fof(f12,axiom,(
% 1.59/0.59    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.59/0.59  fof(f155,plain,(
% 1.59/0.59    k1_xboole_0 != sK1),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f146,f27,f149,f68])).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.59/0.59    inference(forward_demodulation,[],[f66,f25])).
% 1.59/0.59  fof(f25,plain,(
% 1.59/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.59/0.59    inference(cnf_transformation,[],[f8])).
% 1.59/0.59  fof(f66,plain,(
% 1.59/0.59    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 1.59/0.59    inference(superposition,[],[f22,f24])).
% 1.59/0.59  fof(f22,plain,(
% 1.59/0.59    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f16])).
% 1.59/0.59  fof(f16,plain,(
% 1.59/0.59    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.59/0.59    inference(flattening,[],[f15])).
% 1.59/0.59  fof(f15,plain,(
% 1.59/0.59    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f14])).
% 1.59/0.59  fof(f14,negated_conjecture,(
% 1.59/0.59    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.59/0.59    inference(negated_conjecture,[],[f13])).
% 1.59/0.59  fof(f13,conjecture,(
% 1.59/0.59    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.59/0.59  fof(f149,plain,(
% 1.59/0.59    v1_funct_1(k1_xboole_0)),
% 1.59/0.59    inference(superposition,[],[f55,f134])).
% 1.59/0.59  fof(f134,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = sK8(k1_xboole_0,X0)) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f54,f56,f30])).
% 1.59/0.59  fof(f30,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f18])).
% 1.59/0.59  fof(f18,plain,(
% 1.59/0.59    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.59/0.59    inference(flattening,[],[f17])).
% 1.59/0.59  fof(f17,plain,(
% 1.59/0.59    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.59/0.59    inference(ennf_transformation,[],[f9])).
% 1.59/0.59  fof(f9,axiom,(
% 1.59/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.59/0.59  fof(f56,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k1_relat_1(sK8(X0,X1)) = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f21])).
% 1.59/0.59  fof(f21,plain,(
% 1.59/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.59/0.59    inference(ennf_transformation,[],[f11])).
% 1.59/0.59  fof(f11,axiom,(
% 1.59/0.59    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.59/0.59  fof(f54,plain,(
% 1.59/0.59    ( ! [X0,X1] : (v1_relat_1(sK8(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f21])).
% 1.59/0.59  fof(f55,plain,(
% 1.59/0.59    ( ! [X0,X1] : (v1_funct_1(sK8(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f21])).
% 1.59/0.59  fof(f27,plain,(
% 1.59/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f2])).
% 1.59/0.59  fof(f2,axiom,(
% 1.59/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.59/0.59  fof(f146,plain,(
% 1.59/0.59    v1_relat_1(k1_xboole_0)),
% 1.59/0.59    inference(superposition,[],[f26,f133])).
% 1.59/0.59  fof(f133,plain,(
% 1.59/0.59    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f26,f28,f30])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f10])).
% 1.59/0.59  fof(f10,axiom,(
% 1.59/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.59/0.59  fof(f26,plain,(
% 1.59/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f7])).
% 1.59/0.59  fof(f7,axiom,(
% 1.59/0.59    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.59/0.59  fof(f338,plain,(
% 1.59/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f157,f158,f165,f22])).
% 1.59/0.59  fof(f165,plain,(
% 1.59/0.59    ( ! [X0] : (sK1 = k1_relat_1(sK2(sK1,X0))) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f155,f34])).
% 1.59/0.59  fof(f34,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f19])).
% 1.59/0.59  fof(f158,plain,(
% 1.59/0.59    ( ! [X0] : (v1_relat_1(sK2(sK1,X0))) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f155,f32])).
% 1.59/0.59  fof(f32,plain,(
% 1.59/0.59    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f19])).
% 1.59/0.59  fof(f157,plain,(
% 1.59/0.59    ( ! [X0] : (v1_funct_1(sK2(sK1,X0))) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f155,f33])).
% 1.59/0.59  fof(f33,plain,(
% 1.59/0.59    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f19])).
% 1.59/0.59  fof(f347,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(sK3(k1_tarski(X0),sK0),sK0)) )),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f344,f39])).
% 1.59/0.59  fof(f39,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f20])).
% 1.59/0.59  fof(f91,plain,(
% 1.59/0.59    ( ! [X0] : (~sP6(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(global_subsumption,[],[f64,f88])).
% 1.59/0.59  fof(f88,plain,(
% 1.59/0.59    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP6(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(superposition,[],[f61,f24])).
% 1.59/0.59  fof(f61,plain,(
% 1.59/0.59    ( ! [X2,X0] : (r2_hidden(X2,k1_relat_1(X0)) | ~sP6(X2,X0)) )),
% 1.59/0.59    inference(equality_resolution,[],[f46])).
% 1.59/0.59  fof(f46,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~sP6(X2,X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.59/0.59    inference(cnf_transformation,[],[f6])).
% 1.59/0.59  fof(f64,plain,(
% 1.59/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(superposition,[],[f36,f62])).
% 1.59/0.59  fof(f62,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.59/0.59    inference(equality_resolution,[],[f52])).
% 1.59/0.59  fof(f52,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f4])).
% 1.59/0.59  fof(f4,axiom,(
% 1.59/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.59/0.59  fof(f36,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f5])).
% 1.59/0.59  fof(f5,axiom,(
% 1.59/0.59    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.59/0.59  fof(f156,plain,(
% 1.59/0.59    k1_xboole_0 != sK0),
% 1.59/0.59    inference(unit_resulting_resolution,[],[f155,f23])).
% 1.59/0.59  fof(f23,plain,(
% 1.59/0.59    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.59/0.59    inference(cnf_transformation,[],[f16])).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (2838)------------------------------
% 1.59/0.59  % (2838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (2838)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (2838)Memory used [KB]: 7291
% 1.59/0.59  % (2838)Time elapsed: 0.154 s
% 1.59/0.59  % (2838)------------------------------
% 1.59/0.59  % (2838)------------------------------
% 1.59/0.59  % (2813)Success in time 0.217 s
%------------------------------------------------------------------------------
