%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:23 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 160 expanded)
%              Number of leaves         :   12 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 400 expanded)
%              Number of equality atoms :   46 ( 157 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f85])).

fof(f85,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f79,f84])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f81,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X0),sK2) ),
    inference(superposition,[],[f38,f68])).

fof(f68,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f66,f50])).

fof(f50,plain,(
    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

% (17063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (17082)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (17084)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (17067)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (17076)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f23,plain,
    ( ? [X2] :
        ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f48,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f66,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f61,f31])).

fof(f61,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f60,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f30,f49])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f79,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f45,f78])).

fof(f78,plain,(
    ! [X5] : k4_xboole_0(sK0,k4_xboole_0(sK1,X5)) = k3_subset_1(sK0,k4_xboole_0(sK1,X5)) ),
    inference(resolution,[],[f74,f31])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f73,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k7_subset_1(sK0,sK1,X1) ),
    inference(resolution,[],[f25,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f45,plain,(
    k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f43,f42])).

fof(f42,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f25,f31])).

fof(f43,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f27,f40])).

fof(f27,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f116,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f110,f28])).

fof(f110,plain,(
    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f51,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f30,f42])).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:55:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (17062)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (17078)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (17073)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (17079)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.56  % (17080)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.55/0.57  % (17080)Refutation not found, incomplete strategy% (17080)------------------------------
% 1.55/0.57  % (17080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (17080)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (17080)Memory used [KB]: 10618
% 1.55/0.57  % (17080)Time elapsed: 0.119 s
% 1.55/0.57  % (17080)------------------------------
% 1.55/0.57  % (17080)------------------------------
% 1.55/0.57  % (17068)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.55/0.57  % (17066)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.55/0.57  % (17064)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.57  % (17087)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.55/0.58  % (17070)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.55/0.58  % (17092)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.55/0.58  % (17074)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.58  % (17070)Refutation found. Thanks to Tanya!
% 1.55/0.58  % SZS status Theorem for theBenchmark
% 1.55/0.58  % SZS output start Proof for theBenchmark
% 1.55/0.58  fof(f117,plain,(
% 1.55/0.58    $false),
% 1.55/0.58    inference(subsumption_resolution,[],[f116,f85])).
% 1.55/0.58  fof(f85,plain,(
% 1.55/0.58    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.55/0.58    inference(backward_demodulation,[],[f79,f84])).
% 1.55/0.58  fof(f84,plain,(
% 1.55/0.58    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK0,X0))) )),
% 1.55/0.58    inference(forward_demodulation,[],[f81,f28])).
% 1.55/0.58  fof(f28,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f1])).
% 1.55/0.58  fof(f1,axiom,(
% 1.55/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.55/0.58  fof(f81,plain,(
% 1.55/0.58    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 1.55/0.58    inference(superposition,[],[f38,f68])).
% 1.55/0.58  fof(f68,plain,(
% 1.55/0.58    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.55/0.58    inference(forward_demodulation,[],[f66,f50])).
% 1.55/0.58  fof(f50,plain,(
% 1.55/0.58    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 1.55/0.58    inference(backward_demodulation,[],[f48,f49])).
% 1.55/0.58  fof(f49,plain,(
% 1.55/0.58    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 1.55/0.58    inference(resolution,[],[f26,f31])).
% 1.55/0.58  fof(f31,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f15,plain,(
% 1.55/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f5])).
% 1.55/0.58  fof(f5,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.55/0.58  fof(f26,plain,(
% 1.55/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.55/0.58    inference(cnf_transformation,[],[f24])).
% 1.55/0.58  fof(f24,plain,(
% 1.55/0.58    (k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22])).
% 1.55/0.58  fof(f22,plain,(
% 1.55/0.58    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.59  % (17063)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.55/0.59  % (17082)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.55/0.59  % (17084)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.55/0.60  % (17067)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.55/0.60  % (17076)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.55/0.60  fof(f23,plain,(
% 1.55/0.60    ? [X2] : (k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.55/0.60    introduced(choice_axiom,[])).
% 1.55/0.60  fof(f13,plain,(
% 1.55/0.60    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f12])).
% 1.55/0.60  fof(f12,negated_conjecture,(
% 1.55/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.55/0.60    inference(negated_conjecture,[],[f11])).
% 1.55/0.60  fof(f11,conjecture,(
% 1.55/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 1.55/0.60  fof(f48,plain,(
% 1.55/0.60    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 1.55/0.60    inference(resolution,[],[f26,f32])).
% 1.55/0.60  fof(f32,plain,(
% 1.55/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.55/0.60    inference(cnf_transformation,[],[f16])).
% 1.55/0.60  fof(f16,plain,(
% 1.55/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f8])).
% 1.55/0.60  fof(f8,axiom,(
% 1.55/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.55/0.60  fof(f66,plain,(
% 1.55/0.60    k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.55/0.60    inference(resolution,[],[f61,f31])).
% 1.55/0.60  fof(f61,plain,(
% 1.55/0.60    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.55/0.60    inference(subsumption_resolution,[],[f60,f26])).
% 1.55/0.60  fof(f60,plain,(
% 1.55/0.60    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.55/0.60    inference(superposition,[],[f30,f49])).
% 1.55/0.60  fof(f30,plain,(
% 1.55/0.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f14])).
% 1.55/0.60  fof(f14,plain,(
% 1.55/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f6])).
% 1.55/0.60  fof(f6,axiom,(
% 1.55/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.55/0.60  fof(f38,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.55/0.60    inference(definition_unfolding,[],[f34,f29])).
% 1.55/0.60  fof(f29,plain,(
% 1.55/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f2])).
% 1.55/0.60  fof(f2,axiom,(
% 1.55/0.60    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.55/0.60  fof(f34,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f3])).
% 1.55/0.60  fof(f3,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.55/0.60  fof(f79,plain,(
% 1.55/0.60    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.60    inference(backward_demodulation,[],[f45,f78])).
% 1.55/0.60  fof(f78,plain,(
% 1.55/0.60    ( ! [X5] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X5)) = k3_subset_1(sK0,k4_xboole_0(sK1,X5))) )),
% 1.55/0.60    inference(resolution,[],[f74,f31])).
% 1.55/0.60  fof(f74,plain,(
% 1.55/0.60    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) )),
% 1.55/0.60    inference(subsumption_resolution,[],[f73,f25])).
% 1.55/0.60  fof(f25,plain,(
% 1.55/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.60    inference(cnf_transformation,[],[f24])).
% 1.55/0.60  fof(f73,plain,(
% 1.55/0.60    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))) )),
% 1.55/0.60    inference(superposition,[],[f35,f40])).
% 1.55/0.60  fof(f40,plain,(
% 1.55/0.60    ( ! [X1] : (k4_xboole_0(sK1,X1) = k7_subset_1(sK0,sK1,X1)) )),
% 1.55/0.60    inference(resolution,[],[f25,f36])).
% 1.55/0.60  fof(f36,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 1.55/0.60    inference(cnf_transformation,[],[f19])).
% 1.55/0.60  fof(f19,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f10])).
% 1.55/0.60  fof(f10,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.55/0.60  fof(f35,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f18])).
% 1.55/0.60  fof(f18,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(ennf_transformation,[],[f7])).
% 1.55/0.60  fof(f7,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 1.55/0.60  fof(f45,plain,(
% 1.55/0.60    k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)),
% 1.55/0.60    inference(backward_demodulation,[],[f43,f42])).
% 1.55/0.60  fof(f42,plain,(
% 1.55/0.60    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.55/0.60    inference(resolution,[],[f25,f31])).
% 1.55/0.60  fof(f43,plain,(
% 1.55/0.60    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.60    inference(backward_demodulation,[],[f27,f40])).
% 1.55/0.60  fof(f27,plain,(
% 1.55/0.60    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)),
% 1.55/0.60    inference(cnf_transformation,[],[f24])).
% 1.55/0.60  fof(f116,plain,(
% 1.55/0.60    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 1.55/0.60    inference(forward_demodulation,[],[f110,f28])).
% 1.55/0.60  fof(f110,plain,(
% 1.55/0.60    k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 1.55/0.60    inference(resolution,[],[f46,f52])).
% 1.55/0.60  fof(f52,plain,(
% 1.55/0.60    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.55/0.60    inference(subsumption_resolution,[],[f51,f25])).
% 1.55/0.60  fof(f51,plain,(
% 1.55/0.60    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.55/0.60    inference(superposition,[],[f30,f42])).
% 1.55/0.60  fof(f46,plain,(
% 1.55/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK2) = k2_xboole_0(X0,sK2)) )),
% 1.55/0.60    inference(resolution,[],[f26,f37])).
% 1.55/0.60  fof(f37,plain,(
% 1.55/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.55/0.60    inference(cnf_transformation,[],[f21])).
% 1.55/0.60  fof(f21,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.60    inference(flattening,[],[f20])).
% 1.55/0.60  fof(f20,plain,(
% 1.55/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.55/0.60    inference(ennf_transformation,[],[f9])).
% 1.55/0.60  fof(f9,axiom,(
% 1.55/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.55/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.55/0.60  % SZS output end Proof for theBenchmark
% 1.55/0.60  % (17070)------------------------------
% 1.55/0.60  % (17070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.60  % (17070)Termination reason: Refutation
% 1.55/0.60  
% 1.55/0.60  % (17070)Memory used [KB]: 10746
% 1.55/0.60  % (17070)Time elapsed: 0.140 s
% 1.55/0.60  % (17070)------------------------------
% 1.55/0.60  % (17070)------------------------------
% 1.55/0.61  % (17055)Success in time 0.241 s
%------------------------------------------------------------------------------
