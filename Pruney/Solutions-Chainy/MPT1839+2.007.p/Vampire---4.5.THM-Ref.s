%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:02 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   42 (  85 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 229 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1175,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1166,f21])).

fof(f21,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK0,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
      & v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK0,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
   => ( ~ r1_tarski(sK0,sK1)
      & ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(f1166,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f931,f1149])).

fof(f1149,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f930,f20])).

fof(f20,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f930,plain,(
    ! [X2] :
      ( v1_xboole_0(k3_xboole_0(sK0,X2))
      | sK0 = k3_xboole_0(sK0,X2) ) ),
    inference(resolution,[],[f912,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f122,f18])).

fof(f18,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f22,f19])).

fof(f19,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f912,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X2) ),
    inference(trivial_inequality_removal,[],[f893])).

fof(f893,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k3_xboole_0(X2,X3),X2) ) ),
    inference(superposition,[],[f27,f794])).

fof(f794,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f64,f35])).

fof(f35,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f64,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)) = k4_xboole_0(k3_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f29,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f931,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f912,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (25040)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (25048)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (25034)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (25051)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (25056)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (25050)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (25038)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (25055)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (25048)Refutation not found, incomplete strategy% (25048)------------------------------
% 0.20/0.52  % (25048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25047)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (25048)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25048)Memory used [KB]: 6268
% 0.20/0.52  % (25048)Time elapsed: 0.106 s
% 0.20/0.52  % (25048)------------------------------
% 0.20/0.52  % (25048)------------------------------
% 0.20/0.52  % (25037)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (25043)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (25042)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (25037)Refutation not found, incomplete strategy% (25037)------------------------------
% 0.20/0.52  % (25037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25037)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25037)Memory used [KB]: 6140
% 0.20/0.52  % (25037)Time elapsed: 0.115 s
% 0.20/0.52  % (25037)------------------------------
% 0.20/0.52  % (25037)------------------------------
% 0.20/0.52  % (25062)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (25042)Refutation not found, incomplete strategy% (25042)------------------------------
% 0.20/0.52  % (25042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25059)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (25035)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (25054)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (25045)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (25059)Refutation not found, incomplete strategy% (25059)------------------------------
% 0.20/0.52  % (25059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25059)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25053)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (25059)Memory used [KB]: 10618
% 0.20/0.52  % (25059)Time elapsed: 0.117 s
% 0.20/0.52  % (25059)------------------------------
% 0.20/0.52  % (25059)------------------------------
% 0.20/0.52  % (25036)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (25033)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (25055)Refutation not found, incomplete strategy% (25055)------------------------------
% 0.20/0.53  % (25055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25033)Refutation not found, incomplete strategy% (25033)------------------------------
% 0.20/0.53  % (25033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25046)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (25033)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25033)Memory used [KB]: 1663
% 0.20/0.53  % (25033)Time elapsed: 0.131 s
% 0.20/0.53  % (25033)------------------------------
% 0.20/0.53  % (25033)------------------------------
% 0.20/0.53  % (25052)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (25039)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (25043)Refutation not found, incomplete strategy% (25043)------------------------------
% 0.20/0.53  % (25043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25057)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (25055)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25055)Memory used [KB]: 10618
% 0.20/0.53  % (25055)Time elapsed: 0.090 s
% 0.20/0.53  % (25055)------------------------------
% 0.20/0.53  % (25055)------------------------------
% 1.49/0.54  % (25035)Refutation not found, incomplete strategy% (25035)------------------------------
% 1.49/0.54  % (25035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.54  % (25035)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.54  
% 1.49/0.54  % (25035)Memory used [KB]: 10618
% 1.49/0.54  % (25035)Time elapsed: 0.131 s
% 1.49/0.54  % (25035)------------------------------
% 1.49/0.54  % (25035)------------------------------
% 1.49/0.54  % (25043)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.54  
% 1.49/0.54  % (25043)Memory used [KB]: 10618
% 1.49/0.54  % (25043)Time elapsed: 0.129 s
% 1.49/0.54  % (25043)------------------------------
% 1.49/0.54  % (25043)------------------------------
% 1.49/0.54  % (25050)Refutation not found, incomplete strategy% (25050)------------------------------
% 1.49/0.54  % (25050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.54  % (25061)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.54  % (25050)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.54  
% 1.49/0.54  % (25050)Memory used [KB]: 10618
% 1.49/0.54  % (25050)Time elapsed: 0.137 s
% 1.49/0.54  % (25050)------------------------------
% 1.49/0.54  % (25050)------------------------------
% 1.49/0.54  % (25041)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.54  % (25060)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.54  % (25042)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.54  
% 1.49/0.54  % (25042)Memory used [KB]: 10618
% 1.49/0.54  % (25042)Time elapsed: 0.119 s
% 1.49/0.54  % (25042)------------------------------
% 1.49/0.54  % (25042)------------------------------
% 1.49/0.54  % (25049)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.54  % (25044)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (25058)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.61/0.56  % (25058)Refutation not found, incomplete strategy% (25058)------------------------------
% 1.61/0.56  % (25058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.56  % (25058)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.56  
% 1.61/0.56  % (25058)Memory used [KB]: 6140
% 1.61/0.56  % (25058)Time elapsed: 0.155 s
% 1.61/0.56  % (25058)------------------------------
% 1.61/0.56  % (25058)------------------------------
% 1.61/0.57  % (25041)Refutation not found, incomplete strategy% (25041)------------------------------
% 1.61/0.57  % (25041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (25041)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (25041)Memory used [KB]: 10618
% 1.61/0.57  % (25041)Time elapsed: 0.171 s
% 1.61/0.57  % (25041)------------------------------
% 1.61/0.57  % (25041)------------------------------
% 1.61/0.57  % (25040)Refutation found. Thanks to Tanya!
% 1.61/0.57  % SZS status Theorem for theBenchmark
% 1.61/0.57  % SZS output start Proof for theBenchmark
% 1.61/0.57  fof(f1175,plain,(
% 1.61/0.57    $false),
% 1.61/0.57    inference(subsumption_resolution,[],[f1166,f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ~r1_tarski(sK0,sK1)),
% 1.61/0.57    inference(cnf_transformation,[],[f16])).
% 1.61/0.57  fof(f16,plain,(
% 1.61/0.57    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15,f14])).
% 1.61/0.57  fof(f14,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f15,plain,(
% 1.61/0.57    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f11,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 1.61/0.57    inference(flattening,[],[f10])).
% 1.61/0.57  fof(f10,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f9])).
% 1.61/0.57  fof(f9,negated_conjecture,(
% 1.61/0.57    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.61/0.57    inference(negated_conjecture,[],[f8])).
% 1.61/0.57  fof(f8,conjecture,(
% 1.61/0.57    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).
% 1.61/0.57  fof(f1166,plain,(
% 1.61/0.57    r1_tarski(sK0,sK1)),
% 1.61/0.57    inference(superposition,[],[f931,f1149])).
% 1.61/0.57  fof(f1149,plain,(
% 1.61/0.57    sK0 = k3_xboole_0(sK0,sK1)),
% 1.61/0.57    inference(resolution,[],[f930,f20])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 1.61/0.57    inference(cnf_transformation,[],[f16])).
% 1.61/0.57  fof(f930,plain,(
% 1.61/0.57    ( ! [X2] : (v1_xboole_0(k3_xboole_0(sK0,X2)) | sK0 = k3_xboole_0(sK0,X2)) )),
% 1.61/0.57    inference(resolution,[],[f912,f123])).
% 1.61/0.57  fof(f123,plain,(
% 1.61/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(X0)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f122,f18])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ~v1_xboole_0(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f16])).
% 1.61/0.57  fof(f122,plain,(
% 1.61/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 1.61/0.57    inference(resolution,[],[f22,f19])).
% 1.61/0.57  fof(f19,plain,(
% 1.61/0.57    v1_zfmisc_1(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f16])).
% 1.61/0.57  fof(f22,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f13])).
% 1.61/0.57  fof(f13,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.61/0.57    inference(flattening,[],[f12])).
% 1.61/0.57  fof(f12,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f7])).
% 1.61/0.57  fof(f7,axiom,(
% 1.61/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.61/0.57  fof(f912,plain,(
% 1.61/0.57    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 1.61/0.57    inference(trivial_inequality_removal,[],[f893])).
% 1.61/0.57  fof(f893,plain,(
% 1.61/0.57    ( ! [X2,X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 1.61/0.57    inference(superposition,[],[f27,f794])).
% 1.61/0.57  fof(f794,plain,(
% 1.61/0.57    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X5)) )),
% 1.61/0.57    inference(superposition,[],[f64,f35])).
% 1.61/0.57  fof(f35,plain,(
% 1.61/0.57    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 1.61/0.57    inference(resolution,[],[f28,f30])).
% 1.61/0.57  fof(f30,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.61/0.57    inference(superposition,[],[f23,f25])).
% 1.61/0.57  fof(f25,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.61/0.57  fof(f23,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f6])).
% 1.61/0.57  fof(f6,axiom,(
% 1.61/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.61/0.57  fof(f28,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f17])).
% 1.61/0.57  fof(f17,plain,(
% 1.61/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.61/0.57    inference(nnf_transformation,[],[f3])).
% 1.61/0.57  fof(f3,axiom,(
% 1.61/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.61/0.57  fof(f64,plain,(
% 1.61/0.57    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)) = k4_xboole_0(k3_xboole_0(X6,X7),X8)) )),
% 1.61/0.57    inference(superposition,[],[f29,f26])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f5])).
% 1.61/0.58  fof(f5,axiom,(
% 1.61/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.61/0.58  fof(f29,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f17])).
% 1.61/0.58  fof(f931,plain,(
% 1.61/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.61/0.58    inference(superposition,[],[f912,f24])).
% 1.61/0.58  fof(f24,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f2])).
% 1.61/0.58  fof(f2,axiom,(
% 1.61/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.61/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.61/0.58  % SZS output end Proof for theBenchmark
% 1.61/0.58  % (25040)------------------------------
% 1.61/0.58  % (25040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (25040)Termination reason: Refutation
% 1.61/0.58  
% 1.61/0.58  % (25040)Memory used [KB]: 7291
% 1.61/0.58  % (25040)Time elapsed: 0.166 s
% 1.61/0.58  % (25040)------------------------------
% 1.61/0.58  % (25040)------------------------------
% 1.61/0.58  % (25032)Success in time 0.222 s
%------------------------------------------------------------------------------
