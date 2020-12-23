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
% DateTime   : Thu Dec  3 12:48:09 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 171 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  132 ( 389 expanded)
%              Number of equality atoms :   62 ( 194 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f248])).

fof(f248,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f247,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f25,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f247,plain,(
    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f246,f177])).

fof(f177,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f169,f24])).

fof(f24,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f169,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f108,f145,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f145,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f110,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f110,plain,(
    ! [X0,X1] : ~ sP6(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f105,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f105,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f25,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

% (18072)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f108,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f105,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f246,plain,(
    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f239,f211])).

fof(f211,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(unit_resulting_resolution,[],[f105,f202])).

fof(f202,plain,
    ( r2_hidden(sK1(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | r2_hidden(sK1(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | r2_hidden(sK1(sK0),k1_xboole_0) ),
    inference(superposition,[],[f114,f96])).

fof(f96,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k2_relat_1(sK0))
    | k1_xboole_0 = k2_relat_1(sK0)
    | r2_hidden(sK1(sK0),k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k2_relat_1(sK0))
    | k1_xboole_0 = k2_relat_1(sK0)
    | r2_hidden(sK1(sK0),k1_xboole_0)
    | r2_hidden(sK1(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | r2_hidden(sK1(sK0),k1_xboole_0)
      | k1_xboole_0 = k2_relat_1(sK0) ) ),
    inference(global_subsumption,[],[f21,f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK0),k1_xboole_0)
      | ~ r2_hidden(X0,k2_relat_1(sK0))
      | ~ v1_relat_1(sK0)
      | k1_xboole_0 = k2_relat_1(sK0) ) ),
    inference(superposition,[],[f29,f20])).

fof(f20,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ( k1_xboole_0 = k2_relat_1(X0)
            | k1_xboole_0 = k1_relat_1(X0) )
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k2_relat_1(sK0),X1),X1)
      | k2_relat_1(k2_relat_1(sK0)) = X1
      | k1_xboole_0 = k2_relat_1(sK0)
      | r2_hidden(sK1(sK0),k1_xboole_0) ) ),
    inference(resolution,[],[f36,f80])).

fof(f80,plain,(
    ! [X1] :
      ( ~ sP3(X1,k2_relat_1(sK0))
      | k1_xboole_0 = k2_relat_1(sK0)
      | r2_hidden(sK1(sK0),k1_xboole_0) ) ),
    inference(resolution,[],[f77,f32])).

fof(f114,plain,
    ( k1_xboole_0 = k2_relat_1(k2_relat_1(sK0))
    | k1_xboole_0 = k2_relat_1(sK0)
    | r2_hidden(sK1(sK0),k1_xboole_0) ),
    inference(resolution,[],[f105,f88])).

fof(f239,plain,(
    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(unit_resulting_resolution,[],[f21,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f26,f49])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.22/0.54  % (18076)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (18077)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18082)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (18084)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (18090)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (18074)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (18085)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (18068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (18075)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (18082)Refutation not found, incomplete strategy% (18082)------------------------------
% 0.22/0.56  % (18082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18082)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18082)Memory used [KB]: 10746
% 0.22/0.56  % (18082)Time elapsed: 0.134 s
% 0.22/0.56  % (18082)------------------------------
% 0.22/0.56  % (18082)------------------------------
% 0.22/0.56  % (18069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (18066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.51/0.57  % (18065)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.57  % (18081)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.57  % (18070)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.57  % (18073)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.51/0.58  % (18073)Refutation not found, incomplete strategy% (18073)------------------------------
% 1.51/0.58  % (18073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (18087)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.58  % (18079)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.65/0.58  % (18071)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.65/0.58  % (18079)Refutation not found, incomplete strategy% (18079)------------------------------
% 1.65/0.58  % (18079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (18079)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (18079)Memory used [KB]: 10618
% 1.65/0.58  % (18079)Time elapsed: 0.113 s
% 1.65/0.58  % (18079)------------------------------
% 1.65/0.58  % (18079)------------------------------
% 1.65/0.58  % (18064)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.65/0.58  % (18089)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.65/0.58  % (18078)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.65/0.58  % (18071)Refutation not found, incomplete strategy% (18071)------------------------------
% 1.65/0.58  % (18071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (18064)Refutation not found, incomplete strategy% (18064)------------------------------
% 1.65/0.58  % (18064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (18064)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (18064)Memory used [KB]: 10746
% 1.65/0.58  % (18064)Time elapsed: 0.129 s
% 1.65/0.58  % (18064)------------------------------
% 1.65/0.58  % (18064)------------------------------
% 1.65/0.58  % (18088)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.58  % (18071)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (18071)Memory used [KB]: 10618
% 1.65/0.58  % (18071)Time elapsed: 0.123 s
% 1.65/0.58  % (18071)------------------------------
% 1.65/0.58  % (18071)------------------------------
% 1.65/0.58  % (18086)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.65/0.59  % (18091)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.65/0.59  % (18086)Refutation found. Thanks to Tanya!
% 1.65/0.59  % SZS status Theorem for theBenchmark
% 1.65/0.59  % SZS output start Proof for theBenchmark
% 1.65/0.59  fof(f249,plain,(
% 1.65/0.59    $false),
% 1.65/0.59    inference(global_subsumption,[],[f22,f248])).
% 1.65/0.59  fof(f248,plain,(
% 1.65/0.59    k1_xboole_0 = sK0),
% 1.65/0.59    inference(forward_demodulation,[],[f247,f147])).
% 1.65/0.59  fof(f147,plain,(
% 1.65/0.59    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f25,f51])).
% 1.65/0.59  fof(f51,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.59    inference(definition_unfolding,[],[f31,f49])).
% 1.65/0.59  fof(f49,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.65/0.59    inference(definition_unfolding,[],[f27,f48])).
% 1.65/0.59  fof(f48,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.65/0.59    inference(definition_unfolding,[],[f28,f38])).
% 1.65/0.59  fof(f38,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f4])).
% 1.65/0.59  fof(f4,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
% 1.65/0.59  fof(f28,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f3])).
% 1.65/0.59  fof(f3,axiom,(
% 1.65/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.65/0.59  fof(f27,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f7])).
% 1.65/0.59  fof(f7,axiom,(
% 1.65/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.65/0.59  fof(f31,plain,(
% 1.65/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f1])).
% 1.65/0.59  fof(f1,axiom,(
% 1.65/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.65/0.59  fof(f25,plain,(
% 1.65/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f2])).
% 1.65/0.59  fof(f2,axiom,(
% 1.65/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.65/0.59  fof(f247,plain,(
% 1.65/0.59    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k1_xboole_0))),
% 1.65/0.59    inference(forward_demodulation,[],[f246,f177])).
% 1.65/0.59  fof(f177,plain,(
% 1.65/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.65/0.59    inference(forward_demodulation,[],[f169,f24])).
% 1.65/0.59  fof(f24,plain,(
% 1.65/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.65/0.59    inference(cnf_transformation,[],[f11])).
% 1.65/0.59  fof(f11,axiom,(
% 1.65/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.65/0.59  fof(f169,plain,(
% 1.65/0.59    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f108,f145,f36])).
% 1.65/0.59  fof(f36,plain,(
% 1.65/0.59    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.65/0.59    inference(cnf_transformation,[],[f8])).
% 1.65/0.59  fof(f8,axiom,(
% 1.65/0.59    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.65/0.59  fof(f145,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f110,f56])).
% 1.65/0.59  fof(f56,plain,(
% 1.65/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | sP6(X3,X1,X0)) )),
% 1.65/0.59    inference(equality_resolution,[],[f44])).
% 1.65/0.59  fof(f44,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.65/0.59    inference(cnf_transformation,[],[f5])).
% 1.65/0.59  fof(f5,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.65/0.59  fof(f110,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~sP6(X0,k1_xboole_0,X1)) )),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f105,f41])).
% 1.65/0.59  fof(f41,plain,(
% 1.65/0.59    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~sP6(X3,X1,X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f5])).
% 1.65/0.59  fof(f105,plain,(
% 1.65/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f25,f53])).
% 1.65/0.59  fof(f53,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.65/0.59    inference(definition_unfolding,[],[f47,f48])).
% 1.65/0.59  fof(f47,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f19])).
% 1.65/0.59  % (18072)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.65/0.59  fof(f19,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.65/0.59    inference(ennf_transformation,[],[f6])).
% 1.65/0.59  fof(f6,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.65/0.59  fof(f108,plain,(
% 1.65/0.59    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f105,f32])).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~sP3(X2,X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f8])).
% 1.65/0.59  fof(f246,plain,(
% 1.65/0.59    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))),
% 1.65/0.59    inference(forward_demodulation,[],[f239,f211])).
% 1.65/0.59  fof(f211,plain,(
% 1.65/0.59    k1_xboole_0 = k2_relat_1(sK0)),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f105,f202])).
% 1.65/0.59  fof(f202,plain,(
% 1.65/0.59    r2_hidden(sK1(sK0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK0)),
% 1.65/0.59    inference(duplicate_literal_removal,[],[f197])).
% 1.65/0.59  fof(f197,plain,(
% 1.65/0.59    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k2_relat_1(sK0) | r2_hidden(sK1(sK0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK0) | r2_hidden(sK1(sK0),k1_xboole_0)),
% 1.65/0.59    inference(superposition,[],[f114,f96])).
% 1.65/0.59  fof(f96,plain,(
% 1.65/0.59    k2_relat_1(sK0) = k2_relat_1(k2_relat_1(sK0)) | k1_xboole_0 = k2_relat_1(sK0) | r2_hidden(sK1(sK0),k1_xboole_0)),
% 1.65/0.59    inference(duplicate_literal_removal,[],[f93])).
% 1.65/0.59  fof(f93,plain,(
% 1.65/0.59    k2_relat_1(sK0) = k2_relat_1(k2_relat_1(sK0)) | k1_xboole_0 = k2_relat_1(sK0) | r2_hidden(sK1(sK0),k1_xboole_0) | r2_hidden(sK1(sK0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK0)),
% 1.65/0.59    inference(resolution,[],[f88,f77])).
% 1.65/0.59  fof(f77,plain,(
% 1.65/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK0)) | r2_hidden(sK1(sK0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK0)) )),
% 1.65/0.59    inference(global_subsumption,[],[f21,f75])).
% 1.65/0.59  fof(f75,plain,(
% 1.65/0.59    ( ! [X0] : (r2_hidden(sK1(sK0),k1_xboole_0) | ~r2_hidden(X0,k2_relat_1(sK0)) | ~v1_relat_1(sK0) | k1_xboole_0 = k2_relat_1(sK0)) )),
% 1.65/0.59    inference(superposition,[],[f29,f20])).
% 1.65/0.59  fof(f20,plain,(
% 1.65/0.59    k1_xboole_0 = k1_relat_1(sK0) | k1_xboole_0 = k2_relat_1(sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f15])).
% 1.65/0.59  fof(f15,plain,(
% 1.65/0.59    ? [X0] : (k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 1.65/0.59    inference(flattening,[],[f14])).
% 1.65/0.59  fof(f14,plain,(
% 1.65/0.59    ? [X0] : ((k1_xboole_0 != X0 & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f13])).
% 1.65/0.59  fof(f13,negated_conjecture,(
% 1.65/0.59    ~! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.65/0.59    inference(negated_conjecture,[],[f12])).
% 1.65/0.59  fof(f12,conjecture,(
% 1.65/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.65/0.59  fof(f29,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r2_hidden(sK1(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f18])).
% 1.65/0.59  fof(f18,plain,(
% 1.65/0.59    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.65/0.59    inference(flattening,[],[f17])).
% 1.65/0.59  fof(f17,plain,(
% 1.65/0.59    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.65/0.59    inference(ennf_transformation,[],[f9])).
% 1.65/0.59  fof(f9,axiom,(
% 1.65/0.59    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 1.65/0.59  fof(f21,plain,(
% 1.65/0.59    v1_relat_1(sK0)),
% 1.65/0.59    inference(cnf_transformation,[],[f15])).
% 1.65/0.59  fof(f88,plain,(
% 1.65/0.59    ( ! [X1] : (r2_hidden(sK2(k2_relat_1(sK0),X1),X1) | k2_relat_1(k2_relat_1(sK0)) = X1 | k1_xboole_0 = k2_relat_1(sK0) | r2_hidden(sK1(sK0),k1_xboole_0)) )),
% 1.65/0.59    inference(resolution,[],[f36,f80])).
% 1.65/0.59  fof(f80,plain,(
% 1.65/0.59    ( ! [X1] : (~sP3(X1,k2_relat_1(sK0)) | k1_xboole_0 = k2_relat_1(sK0) | r2_hidden(sK1(sK0),k1_xboole_0)) )),
% 1.65/0.59    inference(resolution,[],[f77,f32])).
% 1.65/0.59  fof(f114,plain,(
% 1.65/0.59    k1_xboole_0 = k2_relat_1(k2_relat_1(sK0)) | k1_xboole_0 = k2_relat_1(sK0) | r2_hidden(sK1(sK0),k1_xboole_0)),
% 1.65/0.59    inference(resolution,[],[f105,f88])).
% 1.65/0.59  fof(f239,plain,(
% 1.65/0.59    sK0 = k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 1.65/0.59    inference(unit_resulting_resolution,[],[f21,f50])).
% 1.65/0.59  fof(f50,plain,(
% 1.65/0.59    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.65/0.59    inference(definition_unfolding,[],[f26,f49])).
% 1.65/0.59  fof(f26,plain,(
% 1.65/0.59    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f16])).
% 1.65/0.59  fof(f16,plain,(
% 1.65/0.59    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f10])).
% 1.65/0.59  fof(f10,axiom,(
% 1.65/0.59    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 1.65/0.59  fof(f22,plain,(
% 1.65/0.59    k1_xboole_0 != sK0),
% 1.65/0.59    inference(cnf_transformation,[],[f15])).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (18086)------------------------------
% 1.65/0.59  % (18086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (18086)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (18086)Memory used [KB]: 6396
% 1.65/0.59  % (18086)Time elapsed: 0.170 s
% 1.65/0.59  % (18086)------------------------------
% 1.65/0.59  % (18086)------------------------------
% 1.65/0.59  % (18072)Refutation not found, incomplete strategy% (18072)------------------------------
% 1.65/0.59  % (18072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (18072)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (18072)Memory used [KB]: 10618
% 1.65/0.59  % (18072)Time elapsed: 0.177 s
% 1.65/0.59  % (18072)------------------------------
% 1.65/0.59  % (18072)------------------------------
% 1.65/0.59  % (18070)Refutation not found, incomplete strategy% (18070)------------------------------
% 1.65/0.59  % (18070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (18070)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (18070)Memory used [KB]: 10746
% 1.65/0.59  % (18070)Time elapsed: 0.182 s
% 1.65/0.59  % (18070)------------------------------
% 1.65/0.59  % (18070)------------------------------
% 1.65/0.59  % (18062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.65/0.59  % (18062)Refutation not found, incomplete strategy% (18062)------------------------------
% 1.65/0.59  % (18062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (18062)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (18062)Memory used [KB]: 1663
% 1.65/0.59  % (18062)Time elapsed: 0.176 s
% 1.65/0.59  % (18062)------------------------------
% 1.65/0.59  % (18062)------------------------------
% 1.65/0.59  % (18063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.65/0.60  % (18061)Success in time 0.23 s
%------------------------------------------------------------------------------
