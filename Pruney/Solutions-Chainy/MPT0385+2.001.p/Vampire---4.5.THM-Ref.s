%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:42 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 189 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :   21
%              Number of atoms          :  121 ( 551 expanded)
%              Number of equality atoms :   40 ( 188 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f674,plain,(
    $false ),
    inference(global_subsumption,[],[f671,f673])).

fof(f673,plain,(
    ~ r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f672,f36])).

fof(f36,plain,(
    k1_xboole_0 = k1_setfam_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | k1_setfam_1(k1_xboole_0) != X1 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = X1
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f672,plain,(
    ~ r2_hidden(sK4(k1_setfam_1(k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f560,f13])).

fof(f13,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f560,plain,(
    ~ r2_hidden(sK4(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f51,f557])).

fof(f557,plain,(
    k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f549])).

fof(f549,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f544,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f544,plain,(
    ! [X2] :
      ( r1_tarski(sK0,X2)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f539,f55])).

fof(f55,plain,(
    ~ sP6(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k3_tarski(X0))
      | ~ sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f539,plain,(
    ! [X0,X1] :
      ( sP6(X1,sK0)
      | r1_tarski(sK0,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f531])).

fof(f531,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK0
      | r1_tarski(sK0,X0)
      | sP6(X1,sK0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f517,f84])).

fof(f84,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,sK4(X10,X11))
      | sP6(X9,X10)
      | r1_tarski(X10,X11) ) ),
    inference(resolution,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f28,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f517,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,sK4(sK0,X6))
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,X6) ) ),
    inference(resolution,[],[f505,f26])).

fof(f505,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | r2_hidden(X0,X1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f504,f16])).

fof(f16,plain,(
    ! [X2,X0,X3] :
      ( ~ sP2(X2,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f504,plain,(
    ! [X0] :
      ( sP2(X0,sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sP2(X0,sK0)
      | sP2(X0,sK0) ) ),
    inference(resolution,[],[f496,f14])).

fof(f14,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),X0)
      | sP2(X2,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f496,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0),sK0)
      | k1_xboole_0 = sK0
      | sP2(X0,sK0) ) ),
    inference(resolution,[],[f413,f55])).

fof(f413,plain,(
    ! [X15,X16] :
      ( sP6(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),X15)
      | sP2(X16,X15)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(sK3(X15,X16),sK0) ) ),
    inference(resolution,[],[f83,f100])).

fof(f100,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),X0)
      | k1_xboole_0 = sK0
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f95,f16])).

fof(f95,plain,
    ( sP2(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f39,f48])).

fof(f48,plain,(
    r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),k1_setfam_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f12,f26])).

fof(f12,plain,(
    ~ r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_setfam_1(X0))
      | sP2(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | sP2(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,sK3(X7,X8))
      | sP6(X6,X7)
      | sP2(X8,X7) ) ),
    inference(resolution,[],[f28,f14])).

fof(f51,plain,(
    ~ r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f12,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f671,plain,(
    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f670,f13])).

fof(f670,plain,(
    r2_hidden(sK4(k1_xboole_0,k3_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f559,f36])).

fof(f559,plain,(
    r2_hidden(sK4(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k1_setfam_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f48,f557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (10761)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.49  % (10746)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.26/0.52  % (10745)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.26/0.52  % (10756)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.52  % (10734)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.52  % (10734)Refutation not found, incomplete strategy% (10734)------------------------------
% 1.26/0.52  % (10734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (10734)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (10734)Memory used [KB]: 10618
% 1.26/0.52  % (10734)Time elapsed: 0.117 s
% 1.26/0.52  % (10734)------------------------------
% 1.26/0.52  % (10734)------------------------------
% 1.26/0.53  % (10760)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.53  % (10732)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.53  % (10738)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.53  % (10733)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.53  % (10741)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.26/0.53  % (10749)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.53  % (10747)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.53  % (10752)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.54  % (10748)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.54  % (10739)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (10736)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.54  % (10752)Refutation not found, incomplete strategy% (10752)------------------------------
% 1.39/0.54  % (10752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (10752)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (10752)Memory used [KB]: 10618
% 1.39/0.54  % (10752)Time elapsed: 0.127 s
% 1.39/0.54  % (10752)------------------------------
% 1.39/0.54  % (10752)------------------------------
% 1.39/0.54  % (10740)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.54  % (10753)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.54  % (10740)Refutation not found, incomplete strategy% (10740)------------------------------
% 1.39/0.54  % (10740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (10740)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (10740)Memory used [KB]: 10618
% 1.39/0.54  % (10740)Time elapsed: 0.139 s
% 1.39/0.54  % (10740)------------------------------
% 1.39/0.54  % (10740)------------------------------
% 1.39/0.54  % (10742)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.54  % (10753)Refutation not found, incomplete strategy% (10753)------------------------------
% 1.39/0.54  % (10753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (10753)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (10753)Memory used [KB]: 1663
% 1.39/0.54  % (10753)Time elapsed: 0.139 s
% 1.39/0.54  % (10753)------------------------------
% 1.39/0.54  % (10753)------------------------------
% 1.39/0.54  % (10759)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.54  % (10755)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.54  % (10744)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.56  % (10735)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.56  % (10737)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.56  % (10754)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.56  % (10754)Refutation not found, incomplete strategy% (10754)------------------------------
% 1.39/0.56  % (10754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (10754)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (10754)Memory used [KB]: 10618
% 1.39/0.56  % (10754)Time elapsed: 0.143 s
% 1.39/0.56  % (10754)------------------------------
% 1.39/0.56  % (10754)------------------------------
% 1.39/0.57  % (10757)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.57  % (10750)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.57  % (10751)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.57  % (10756)Refutation found. Thanks to Tanya!
% 1.39/0.57  % SZS status Theorem for theBenchmark
% 1.39/0.57  % SZS output start Proof for theBenchmark
% 1.39/0.57  fof(f674,plain,(
% 1.39/0.57    $false),
% 1.39/0.57    inference(global_subsumption,[],[f671,f673])).
% 1.39/0.57  fof(f673,plain,(
% 1.39/0.57    ~r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.39/0.57    inference(forward_demodulation,[],[f672,f36])).
% 1.39/0.57  fof(f36,plain,(
% 1.39/0.57    k1_xboole_0 = k1_setfam_1(k1_xboole_0)),
% 1.39/0.57    inference(equality_resolution,[],[f35])).
% 1.39/0.57  fof(f35,plain,(
% 1.39/0.57    ( ! [X1] : (k1_xboole_0 = X1 | k1_setfam_1(k1_xboole_0) != X1) )),
% 1.39/0.57    inference(equality_resolution,[],[f22])).
% 1.39/0.57  fof(f22,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = X1 | k1_setfam_1(X0) != X1) )),
% 1.39/0.57    inference(cnf_transformation,[],[f9])).
% 1.39/0.57  fof(f9,plain,(
% 1.39/0.57    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.39/0.57    inference(ennf_transformation,[],[f5])).
% 1.39/0.57  fof(f5,axiom,(
% 1.39/0.57    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.39/0.57  fof(f672,plain,(
% 1.39/0.57    ~r2_hidden(sK4(k1_setfam_1(k1_xboole_0),k1_xboole_0),k1_xboole_0)),
% 1.39/0.57    inference(forward_demodulation,[],[f560,f13])).
% 1.39/0.57  fof(f13,plain,(
% 1.39/0.57    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.39/0.57    inference(cnf_transformation,[],[f4])).
% 1.39/0.57  fof(f4,axiom,(
% 1.39/0.57    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.39/0.57  fof(f560,plain,(
% 1.39/0.57    ~r2_hidden(sK4(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0))),
% 1.39/0.57    inference(backward_demodulation,[],[f51,f557])).
% 1.39/0.57  fof(f557,plain,(
% 1.39/0.57    k1_xboole_0 = sK0),
% 1.39/0.57    inference(duplicate_literal_removal,[],[f549])).
% 1.39/0.57  fof(f549,plain,(
% 1.39/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.39/0.57    inference(resolution,[],[f544,f23])).
% 1.39/0.57  fof(f23,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.39/0.57    inference(cnf_transformation,[],[f10])).
% 1.39/0.57  fof(f10,plain,(
% 1.39/0.57    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(ennf_transformation,[],[f3])).
% 1.39/0.57  fof(f3,axiom,(
% 1.39/0.57    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.39/0.57  fof(f544,plain,(
% 1.39/0.57    ( ! [X2] : (r1_tarski(sK0,X2) | k1_xboole_0 = sK0) )),
% 1.39/0.57    inference(resolution,[],[f539,f55])).
% 1.39/0.57  fof(f55,plain,(
% 1.39/0.57    ~sP6(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),sK0)),
% 1.39/0.57    inference(unit_resulting_resolution,[],[f51,f42])).
% 1.39/0.57  fof(f42,plain,(
% 1.39/0.57    ( ! [X2,X0] : (r2_hidden(X2,k3_tarski(X0)) | ~sP6(X2,X0)) )),
% 1.39/0.57    inference(equality_resolution,[],[f31])).
% 1.39/0.57  fof(f31,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (~sP6(X2,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 1.39/0.57    inference(cnf_transformation,[],[f2])).
% 1.39/0.57  fof(f2,axiom,(
% 1.39/0.57    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.39/0.57  fof(f539,plain,(
% 1.39/0.57    ( ! [X0,X1] : (sP6(X1,sK0) | r1_tarski(sK0,X0) | k1_xboole_0 = sK0) )),
% 1.39/0.57    inference(duplicate_literal_removal,[],[f531])).
% 1.39/0.57  fof(f531,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k1_xboole_0 = sK0 | r1_tarski(sK0,X0) | sP6(X1,sK0) | r1_tarski(sK0,X0)) )),
% 1.39/0.57    inference(resolution,[],[f517,f84])).
% 1.39/0.57  fof(f84,plain,(
% 1.39/0.57    ( ! [X10,X11,X9] : (~r2_hidden(X9,sK4(X10,X11)) | sP6(X9,X10) | r1_tarski(X10,X11)) )),
% 1.39/0.57    inference(resolution,[],[f28,f26])).
% 1.39/0.57  fof(f26,plain,(
% 1.39/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f11])).
% 1.39/0.57  fof(f11,plain,(
% 1.39/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.57    inference(ennf_transformation,[],[f1])).
% 1.39/0.57  fof(f1,axiom,(
% 1.39/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.57  fof(f28,plain,(
% 1.39/0.57    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3) | sP6(X2,X0)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f2])).
% 1.39/0.57  fof(f517,plain,(
% 1.39/0.57    ( ! [X6,X5] : (r2_hidden(X5,sK4(sK0,X6)) | k1_xboole_0 = sK0 | r1_tarski(sK0,X6)) )),
% 1.39/0.57    inference(resolution,[],[f505,f26])).
% 1.39/0.57  fof(f505,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | r2_hidden(X0,X1) | k1_xboole_0 = sK0) )),
% 1.39/0.57    inference(resolution,[],[f504,f16])).
% 1.39/0.57  fof(f16,plain,(
% 1.39/0.57    ( ! [X2,X0,X3] : (~sP2(X2,X0) | r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f9])).
% 1.39/0.57  fof(f504,plain,(
% 1.39/0.57    ( ! [X0] : (sP2(X0,sK0) | k1_xboole_0 = sK0) )),
% 1.39/0.57    inference(duplicate_literal_removal,[],[f501])).
% 1.39/0.57  fof(f501,plain,(
% 1.39/0.57    ( ! [X0] : (k1_xboole_0 = sK0 | sP2(X0,sK0) | sP2(X0,sK0)) )),
% 1.39/0.57    inference(resolution,[],[f496,f14])).
% 1.39/0.57  fof(f14,plain,(
% 1.39/0.57    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),X0) | sP2(X2,X0)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f9])).
% 1.39/0.57  fof(f496,plain,(
% 1.39/0.57    ( ! [X0] : (~r2_hidden(sK3(sK0,X0),sK0) | k1_xboole_0 = sK0 | sP2(X0,sK0)) )),
% 1.39/0.57    inference(resolution,[],[f413,f55])).
% 1.39/0.57  fof(f413,plain,(
% 1.39/0.57    ( ! [X15,X16] : (sP6(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),X15) | sP2(X16,X15) | k1_xboole_0 = sK0 | ~r2_hidden(sK3(X15,X16),sK0)) )),
% 1.39/0.57    inference(resolution,[],[f83,f100])).
% 1.39/0.57  fof(f100,plain,(
% 1.39/0.57    ( ! [X0] : (r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),X0) | k1_xboole_0 = sK0 | ~r2_hidden(X0,sK0)) )),
% 1.39/0.57    inference(resolution,[],[f95,f16])).
% 1.39/0.57  fof(f95,plain,(
% 1.39/0.57    sP2(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),sK0) | k1_xboole_0 = sK0),
% 1.39/0.57    inference(resolution,[],[f39,f48])).
% 1.39/0.57  fof(f48,plain,(
% 1.39/0.57    r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),k1_setfam_1(sK0))),
% 1.39/0.57    inference(unit_resulting_resolution,[],[f12,f26])).
% 1.39/0.57  fof(f12,plain,(
% 1.39/0.57    ~r1_tarski(k1_setfam_1(sK0),k3_tarski(sK0))),
% 1.39/0.57    inference(cnf_transformation,[],[f8])).
% 1.39/0.57  fof(f8,plain,(
% 1.39/0.57    ? [X0] : ~r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 1.39/0.57    inference(ennf_transformation,[],[f7])).
% 1.39/0.57  fof(f7,negated_conjecture,(
% 1.39/0.57    ~! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 1.39/0.57    inference(negated_conjecture,[],[f6])).
% 1.39/0.57  fof(f6,conjecture,(
% 1.39/0.57    ! [X0] : r1_tarski(k1_setfam_1(X0),k3_tarski(X0))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_setfam_1)).
% 1.39/0.57  fof(f39,plain,(
% 1.39/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_setfam_1(X0)) | sP2(X2,X0) | k1_xboole_0 = X0) )),
% 1.39/0.57    inference(equality_resolution,[],[f18])).
% 1.39/0.57  fof(f18,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | sP2(X2,X0) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 1.39/0.57    inference(cnf_transformation,[],[f9])).
% 1.39/0.57  fof(f83,plain,(
% 1.39/0.57    ( ! [X6,X8,X7] : (~r2_hidden(X6,sK3(X7,X8)) | sP6(X6,X7) | sP2(X8,X7)) )),
% 1.39/0.57    inference(resolution,[],[f28,f14])).
% 1.39/0.57  fof(f51,plain,(
% 1.39/0.57    ~r2_hidden(sK4(k1_setfam_1(sK0),k3_tarski(sK0)),k3_tarski(sK0))),
% 1.39/0.57    inference(unit_resulting_resolution,[],[f12,f27])).
% 1.39/0.57  fof(f27,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f11])).
% 1.39/0.57  fof(f671,plain,(
% 1.39/0.57    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.39/0.57    inference(forward_demodulation,[],[f670,f13])).
% 1.39/0.57  fof(f670,plain,(
% 1.39/0.57    r2_hidden(sK4(k1_xboole_0,k3_tarski(k1_xboole_0)),k1_xboole_0)),
% 1.39/0.57    inference(forward_demodulation,[],[f559,f36])).
% 1.39/0.57  fof(f559,plain,(
% 1.39/0.57    r2_hidden(sK4(k1_setfam_1(k1_xboole_0),k3_tarski(k1_xboole_0)),k1_setfam_1(k1_xboole_0))),
% 1.39/0.57    inference(backward_demodulation,[],[f48,f557])).
% 1.39/0.57  % SZS output end Proof for theBenchmark
% 1.39/0.57  % (10756)------------------------------
% 1.39/0.57  % (10756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (10756)Termination reason: Refutation
% 1.39/0.57  
% 1.39/0.57  % (10756)Memory used [KB]: 6908
% 1.39/0.57  % (10756)Time elapsed: 0.164 s
% 1.39/0.57  % (10756)------------------------------
% 1.39/0.57  % (10756)------------------------------
% 1.39/0.57  % (10743)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.58  % (10731)Success in time 0.219 s
%------------------------------------------------------------------------------
