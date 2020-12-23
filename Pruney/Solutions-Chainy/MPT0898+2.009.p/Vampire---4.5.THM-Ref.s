%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 402 expanded)
%              Number of leaves         :    5 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          :  118 ( 736 expanded)
%              Number of equality atoms :  117 ( 735 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,plain,(
    $false ),
    inference(subsumption_resolution,[],[f462,f436])).

fof(f436,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f10,f420])).

fof(f420,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f417])).

fof(f417,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(equality_factoring,[],[f365])).

fof(f365,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f364,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f364,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f341,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f341,plain,(
    ! [X0] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f21,f293])).

fof(f293,plain,(
    ! [X18] :
      ( k1_xboole_0 = X18
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f279,f46])).

fof(f46,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f37,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f27,f27])).

fof(f37,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3) ),
    inference(superposition,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X2 ) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f279,plain,(
    ! [X18] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X18)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = X18
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X18] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X18)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK0
      | k1_xboole_0 = X18
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f26,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f211,f26])).

fof(f211,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(forward_demodulation,[],[f202,f46])).

fof(f202,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(superposition,[],[f21,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f195,f10])).

fof(f195,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(superposition,[],[f91,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f91,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(superposition,[],[f12,f21])).

fof(f21,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f9,f20,f20])).

fof(f9,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f10,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f462,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f451,f29])).

fof(f29,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f451,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f276,f420])).

fof(f276,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f26,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.55  % (12284)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (12294)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (12288)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.56  % (12286)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.56  % (12300)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (12285)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.57  % (12282)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.57  % (12282)Refutation not found, incomplete strategy% (12282)------------------------------
% 0.20/0.57  % (12282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (12282)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (12282)Memory used [KB]: 1663
% 0.20/0.57  % (12282)Time elapsed: 0.144 s
% 0.20/0.57  % (12282)------------------------------
% 0.20/0.57  % (12282)------------------------------
% 0.20/0.57  % (12292)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.58  % (12292)Refutation not found, incomplete strategy% (12292)------------------------------
% 0.20/0.58  % (12292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (12287)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.58  % (12292)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (12292)Memory used [KB]: 10618
% 0.20/0.58  % (12292)Time elapsed: 0.146 s
% 0.20/0.58  % (12292)------------------------------
% 0.20/0.58  % (12292)------------------------------
% 0.20/0.58  % (12302)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.58  % (12304)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.59  % (12297)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.59  % (12297)Refutation not found, incomplete strategy% (12297)------------------------------
% 0.20/0.59  % (12297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (12297)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (12297)Memory used [KB]: 6140
% 0.20/0.59  % (12297)Time elapsed: 0.002 s
% 0.20/0.59  % (12297)------------------------------
% 0.20/0.59  % (12297)------------------------------
% 0.20/0.59  % (12283)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.59  % (12310)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.59  % (12298)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.60  % (12302)Refutation not found, incomplete strategy% (12302)------------------------------
% 0.20/0.60  % (12302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (12303)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.60  % (12307)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.60  % (12302)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (12302)Memory used [KB]: 10746
% 0.20/0.60  % (12302)Time elapsed: 0.163 s
% 0.20/0.60  % (12302)------------------------------
% 0.20/0.60  % (12302)------------------------------
% 0.20/0.60  % (12306)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.60  % (12306)Refutation not found, incomplete strategy% (12306)------------------------------
% 0.20/0.60  % (12306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (12306)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (12306)Memory used [KB]: 1663
% 0.20/0.60  % (12306)Time elapsed: 0.125 s
% 0.20/0.60  % (12306)------------------------------
% 0.20/0.60  % (12306)------------------------------
% 0.20/0.60  % (12312)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.60  % (12288)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % (12301)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.60  % (12289)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.60  % (12293)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.61  % (12293)Refutation not found, incomplete strategy% (12293)------------------------------
% 0.20/0.61  % (12293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (12293)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.61  
% 0.20/0.61  % (12293)Memory used [KB]: 10618
% 0.20/0.61  % (12293)Time elapsed: 0.172 s
% 0.20/0.61  % (12293)------------------------------
% 0.20/0.61  % (12293)------------------------------
% 0.20/0.61  % (12290)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.61  % (12296)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.61  % (12295)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.62  % SZS output start Proof for theBenchmark
% 0.20/0.62  fof(f463,plain,(
% 0.20/0.62    $false),
% 0.20/0.62    inference(subsumption_resolution,[],[f462,f436])).
% 0.20/0.62  fof(f436,plain,(
% 0.20/0.62    k1_xboole_0 != sK1),
% 0.20/0.62    inference(backward_demodulation,[],[f10,f420])).
% 0.20/0.62  fof(f420,plain,(
% 0.20/0.62    k1_xboole_0 = sK0),
% 0.20/0.62    inference(trivial_inequality_removal,[],[f417])).
% 0.20/0.62  fof(f417,plain,(
% 0.20/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.20/0.62    inference(equality_factoring,[],[f365])).
% 0.20/0.62  fof(f365,plain,(
% 0.20/0.62    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK0) )),
% 0.20/0.62    inference(subsumption_resolution,[],[f364,f26])).
% 0.20/0.62  fof(f26,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.20/0.62    inference(definition_unfolding,[],[f15,f20])).
% 0.20/0.62  fof(f20,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.62    inference(definition_unfolding,[],[f14,f13])).
% 0.20/0.62  fof(f13,plain,(
% 0.20/0.62    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.62    inference(cnf_transformation,[],[f2])).
% 0.20/0.62  fof(f2,axiom,(
% 0.20/0.62    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.62  fof(f14,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.62    inference(cnf_transformation,[],[f3])).
% 0.20/0.62  fof(f3,axiom,(
% 0.20/0.62    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.62  fof(f15,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.20/0.62    inference(cnf_transformation,[],[f4])).
% 0.20/0.62  fof(f4,axiom,(
% 0.20/0.62    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.20/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.20/0.62  fof(f364,plain,(
% 0.20/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = X0 | k1_xboole_0 = sK0) )),
% 0.20/0.62    inference(forward_demodulation,[],[f341,f27])).
% 0.20/0.62  fof(f27,plain,(
% 0.20/0.62    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 0.20/0.62    inference(equality_resolution,[],[f22])).
% 0.20/0.62  fof(f22,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X3) )),
% 0.20/0.62    inference(definition_unfolding,[],[f19,f20])).
% 0.20/0.62  fof(f19,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X3) )),
% 0.20/0.62    inference(cnf_transformation,[],[f4])).
% 0.20/0.62  fof(f341,plain,(
% 0.20/0.62    ( ! [X0] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = sK0) )),
% 0.20/0.62    inference(superposition,[],[f21,f293])).
% 0.20/0.62  fof(f293,plain,(
% 0.20/0.62    ( ! [X18] : (k1_xboole_0 = X18 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.20/0.62    inference(subsumption_resolution,[],[f279,f46])).
% 0.20/0.62  fof(f46,plain,(
% 0.20/0.62    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 0.20/0.62    inference(forward_demodulation,[],[f37,f32])).
% 0.20/0.62  fof(f32,plain,(
% 0.20/0.62    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.62    inference(superposition,[],[f27,f27])).
% 0.20/0.62  fof(f37,plain,(
% 0.20/0.62    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),X3)) )),
% 0.20/0.62    inference(superposition,[],[f28,f27])).
% 0.20/0.62  fof(f28,plain,(
% 0.20/0.62    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 0.20/0.62    inference(equality_resolution,[],[f23])).
% 0.20/0.62  fof(f23,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X2) )),
% 0.20/0.62    inference(definition_unfolding,[],[f18,f20])).
% 0.20/0.62  fof(f18,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X2) )),
% 0.20/0.62    inference(cnf_transformation,[],[f4])).
% 0.20/0.62  fof(f279,plain,(
% 0.20/0.62    ( ! [X18] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X18) | k1_xboole_0 = sK0 | k1_xboole_0 = X18 | k1_xboole_0 = sK1) )),
% 0.20/0.62    inference(duplicate_literal_removal,[],[f265])).
% 0.20/0.62  fof(f265,plain,(
% 0.20/0.62    ( ! [X18] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X18) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = X18 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.20/0.62    inference(superposition,[],[f26,f212])).
% 0.20/0.62  fof(f212,plain,(
% 0.20/0.62    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.20/0.62    inference(subsumption_resolution,[],[f211,f26])).
% 0.20/0.62  fof(f211,plain,(
% 0.20/0.62    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.20/0.62    inference(forward_demodulation,[],[f202,f46])).
% 0.20/0.62  fof(f202,plain,(
% 0.20/0.62    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.20/0.62    inference(superposition,[],[f21,f197])).
% 0.20/0.62  fof(f197,plain,(
% 0.20/0.62    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.20/0.62    inference(subsumption_resolution,[],[f195,f10])).
% 0.20/0.62  fof(f195,plain,(
% 0.20/0.62    sK0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.20/0.62    inference(superposition,[],[f91,f12])).
% 0.20/0.62  fof(f12,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.62    inference(cnf_transformation,[],[f8])).
% 0.20/0.62  fof(f8,plain,(
% 0.20/0.62    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.62    inference(ennf_transformation,[],[f1])).
% 0.20/0.62  fof(f1,axiom,(
% 0.20/0.62    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.20/0.62  fof(f91,plain,(
% 0.20/0.62    sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.20/0.62    inference(superposition,[],[f12,f21])).
% 0.20/0.62  fof(f21,plain,(
% 0.20/0.62    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.20/0.62    inference(definition_unfolding,[],[f9,f20,f20])).
% 0.20/0.62  fof(f9,plain,(
% 0.20/0.62    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.20/0.62    inference(cnf_transformation,[],[f7])).
% 0.20/0.62  fof(f7,plain,(
% 0.20/0.62    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.20/0.62    inference(ennf_transformation,[],[f6])).
% 0.20/0.62  fof(f6,negated_conjecture,(
% 0.20/0.62    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.20/0.62    inference(negated_conjecture,[],[f5])).
% 0.20/0.62  fof(f5,conjecture,(
% 0.20/0.62    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.20/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.20/0.62  fof(f10,plain,(
% 0.20/0.62    sK0 != sK1),
% 0.20/0.62    inference(cnf_transformation,[],[f7])).
% 0.20/0.62  fof(f462,plain,(
% 0.20/0.62    k1_xboole_0 = sK1),
% 0.20/0.62    inference(subsumption_resolution,[],[f451,f29])).
% 0.20/0.62  fof(f29,plain,(
% 0.20/0.62    ( ! [X2,X0,X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3)) )),
% 0.20/0.62    inference(equality_resolution,[],[f24])).
% 0.20/0.62  fof(f24,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 != X1) )),
% 0.20/0.62    inference(definition_unfolding,[],[f17,f20])).
% 0.20/0.62  fof(f17,plain,(
% 0.20/0.62    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 != X1) )),
% 0.20/0.62    inference(cnf_transformation,[],[f4])).
% 0.20/0.62  fof(f451,plain,(
% 0.20/0.62    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK1),
% 0.20/0.62    inference(backward_demodulation,[],[f276,f420])).
% 0.20/0.62  fof(f276,plain,(
% 0.20/0.62    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1),
% 0.20/0.62    inference(duplicate_literal_removal,[],[f275])).
% 0.20/0.62  fof(f275,plain,(
% 0.20/0.62    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.20/0.62    inference(superposition,[],[f26,f21])).
% 0.20/0.62  % SZS output end Proof for theBenchmark
% 0.20/0.62  % (12288)------------------------------
% 0.20/0.62  % (12288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (12288)Termination reason: Refutation
% 0.20/0.62  
% 0.20/0.62  % (12288)Memory used [KB]: 6396
% 0.20/0.62  % (12288)Time elapsed: 0.162 s
% 0.20/0.62  % (12288)------------------------------
% 0.20/0.62  % (12288)------------------------------
% 0.20/0.62  % (12281)Success in time 0.255 s
%------------------------------------------------------------------------------
