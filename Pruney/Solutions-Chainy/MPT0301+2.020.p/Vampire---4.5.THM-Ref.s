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
% DateTime   : Thu Dec  3 12:41:55 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 208 expanded)
%              Number of leaves         :    6 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  117 ( 393 expanded)
%              Number of equality atoms :   71 ( 229 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f655,plain,(
    $false ),
    inference(subsumption_resolution,[],[f653,f618])).

fof(f618,plain,(
    ! [X10] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X10) ),
    inference(resolution,[],[f493,f43])).

fof(f43,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f30,f12])).

fof(f12,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

% (11306)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f21,f13])).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f493,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK6(X5,X6,sK2(k1_xboole_0,k2_zfmisc_1(X5,X6))),X5)
      | k1_xboole_0 = k2_zfmisc_1(X5,X6) ) ),
    inference(forward_demodulation,[],[f125,f124])).

fof(f124,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f90,f43])).

fof(f90,plain,(
    ! [X7] :
      ( r2_hidden(sK2(k1_xboole_0,X7),X7)
      | k3_tarski(k1_xboole_0) = X7 ) ),
    inference(resolution,[],[f16,f43])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f125,plain,(
    ! [X6,X5] :
      ( k3_tarski(k1_xboole_0) = k2_zfmisc_1(X5,X6)
      | r2_hidden(sK6(X5,X6,sK2(k1_xboole_0,k2_zfmisc_1(X5,X6))),X5) ) ),
    inference(resolution,[],[f90,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK6(X0,X1,X3),X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f653,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(trivial_inequality_removal,[],[f652])).

fof(f652,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f41,f650])).

fof(f650,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f644])).

fof(f644,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f612,f634])).

fof(f634,plain,(
    ! [X10] : k1_xboole_0 = k2_zfmisc_1(X10,k1_xboole_0) ),
    inference(resolution,[],[f494,f43])).

fof(f494,plain,(
    ! [X8,X7] :
      ( r2_hidden(sK7(X7,X8,sK2(k1_xboole_0,k2_zfmisc_1(X7,X8))),X8)
      | k1_xboole_0 = k2_zfmisc_1(X7,X8) ) ),
    inference(forward_demodulation,[],[f126,f124])).

fof(f126,plain,(
    ! [X8,X7] :
      ( k3_tarski(k1_xboole_0) = k2_zfmisc_1(X7,X8)
      | r2_hidden(sK7(X7,X8,sK2(k1_xboole_0,k2_zfmisc_1(X7,X8))),X8) ) ),
    inference(resolution,[],[f90,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f612,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f611])).

fof(f611,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f40,f609])).

fof(f609,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f604])).

fof(f604,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f602,f160])).

fof(f160,plain,(
    ! [X7] :
      ( r2_hidden(sK2(k1_xboole_0,X7),X7)
      | k1_xboole_0 = X7 ) ),
    inference(backward_demodulation,[],[f90,f124])).

fof(f602,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f601,f43])).

fof(f601,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,sK1)),k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f600])).

fof(f600,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,sK1)),k1_xboole_0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f181,f11])).

fof(f11,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,sK2(k1_xboole_0,X0)),k2_zfmisc_1(X2,X0))
      | ~ r2_hidden(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f122,f124])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_xboole_0) = X0
      | ~ r2_hidden(X1,X2)
      | r2_hidden(k4_tarski(X1,sK2(k1_xboole_0,X0)),k2_zfmisc_1(X2,X0)) ) ),
    inference(resolution,[],[f90,f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f10])).

fof(f10,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f9])).

fof(f9,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (11295)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (11300)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (11297)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (11302)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (11302)Refutation not found, incomplete strategy% (11302)------------------------------
% 0.20/0.51  % (11302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11302)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11302)Memory used [KB]: 10618
% 0.20/0.51  % (11302)Time elapsed: 0.104 s
% 0.20/0.51  % (11302)------------------------------
% 0.20/0.51  % (11302)------------------------------
% 1.23/0.52  % (11294)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.52  % (11310)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.52  % (11313)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.23/0.53  % (11317)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.23/0.53  % (11308)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.53  % (11305)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.53  % (11296)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.53  % (11311)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.53  % (11296)Refutation not found, incomplete strategy% (11296)------------------------------
% 1.23/0.53  % (11296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (11296)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (11296)Memory used [KB]: 10618
% 1.23/0.53  % (11296)Time elapsed: 0.127 s
% 1.23/0.53  % (11296)------------------------------
% 1.23/0.53  % (11296)------------------------------
% 1.23/0.53  % (11298)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.53  % (11311)Refutation not found, incomplete strategy% (11311)------------------------------
% 1.23/0.53  % (11311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (11311)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (11311)Memory used [KB]: 10618
% 1.23/0.53  % (11311)Time elapsed: 0.127 s
% 1.23/0.53  % (11311)------------------------------
% 1.23/0.53  % (11311)------------------------------
% 1.23/0.53  % (11298)Refutation not found, incomplete strategy% (11298)------------------------------
% 1.23/0.53  % (11298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (11320)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.54  % (11322)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.54  % (11303)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.54  % (11309)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.54  % (11294)Refutation not found, incomplete strategy% (11294)------------------------------
% 1.39/0.54  % (11294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (11321)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.54  % (11323)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.54  % (11301)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.54  % (11294)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (11294)Memory used [KB]: 1663
% 1.39/0.54  % (11294)Time elapsed: 0.115 s
% 1.39/0.54  % (11294)------------------------------
% 1.39/0.54  % (11294)------------------------------
% 1.39/0.54  % (11312)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.54  % (11319)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.54  % (11314)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.54  % (11319)Refutation not found, incomplete strategy% (11319)------------------------------
% 1.39/0.54  % (11319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (11319)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (11319)Memory used [KB]: 6268
% 1.39/0.54  % (11319)Time elapsed: 0.138 s
% 1.39/0.54  % (11319)------------------------------
% 1.39/0.54  % (11319)------------------------------
% 1.39/0.54  % (11309)Refutation not found, incomplete strategy% (11309)------------------------------
% 1.39/0.54  % (11309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (11314)Refutation not found, incomplete strategy% (11314)------------------------------
% 1.39/0.54  % (11314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (11314)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (11314)Memory used [KB]: 10746
% 1.39/0.54  % (11314)Time elapsed: 0.139 s
% 1.39/0.54  % (11314)------------------------------
% 1.39/0.54  % (11314)------------------------------
% 1.39/0.54  % (11309)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (11309)Memory used [KB]: 6140
% 1.39/0.54  % (11309)Time elapsed: 0.004 s
% 1.39/0.54  % (11309)------------------------------
% 1.39/0.54  % (11309)------------------------------
% 1.39/0.54  % (11315)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.54  % (11305)Refutation not found, incomplete strategy% (11305)------------------------------
% 1.39/0.54  % (11305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (11305)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (11305)Memory used [KB]: 10618
% 1.39/0.54  % (11305)Time elapsed: 0.153 s
% 1.39/0.54  % (11305)------------------------------
% 1.39/0.54  % (11305)------------------------------
% 1.39/0.55  % (11316)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.55  % (11304)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.55  % (11316)Refutation not found, incomplete strategy% (11316)------------------------------
% 1.39/0.55  % (11316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (11316)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (11316)Memory used [KB]: 10746
% 1.39/0.55  % (11316)Time elapsed: 0.151 s
% 1.39/0.55  % (11316)------------------------------
% 1.39/0.55  % (11316)------------------------------
% 1.39/0.55  % (11300)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f655,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(subsumption_resolution,[],[f653,f618])).
% 1.39/0.55  fof(f618,plain,(
% 1.39/0.55    ( ! [X10] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X10)) )),
% 1.39/0.55    inference(resolution,[],[f493,f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.39/0.55    inference(trivial_inequality_removal,[],[f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.39/0.55    inference(superposition,[],[f30,f12])).
% 1.39/0.55  fof(f12,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f1])).
% 1.39/0.55  % (11306)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.39/0.55    inference(definition_unfolding,[],[f21,f13])).
% 1.39/0.55  fof(f13,plain,(
% 1.39/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.39/0.55  fof(f493,plain,(
% 1.39/0.55    ( ! [X6,X5] : (r2_hidden(sK6(X5,X6,sK2(k1_xboole_0,k2_zfmisc_1(X5,X6))),X5) | k1_xboole_0 = k2_zfmisc_1(X5,X6)) )),
% 1.39/0.55    inference(forward_demodulation,[],[f125,f124])).
% 1.39/0.55  fof(f124,plain,(
% 1.39/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.39/0.55    inference(resolution,[],[f90,f43])).
% 1.39/0.55  fof(f90,plain,(
% 1.39/0.55    ( ! [X7] : (r2_hidden(sK2(k1_xboole_0,X7),X7) | k3_tarski(k1_xboole_0) = X7) )),
% 1.39/0.55    inference(resolution,[],[f16,f43])).
% 1.39/0.55  fof(f16,plain,(
% 1.39/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 1.39/0.55  fof(f125,plain,(
% 1.39/0.55    ( ! [X6,X5] : (k3_tarski(k1_xboole_0) = k2_zfmisc_1(X5,X6) | r2_hidden(sK6(X5,X6,sK2(k1_xboole_0,k2_zfmisc_1(X5,X6))),X5)) )),
% 1.39/0.55    inference(resolution,[],[f90,f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | r2_hidden(sK6(X0,X1,X3),X0)) )),
% 1.39/0.55    inference(equality_resolution,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.39/0.55  fof(f653,plain,(
% 1.39/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.39/0.55    inference(trivial_inequality_removal,[],[f652])).
% 1.39/0.55  fof(f652,plain,(
% 1.39/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.39/0.55    inference(backward_demodulation,[],[f41,f650])).
% 1.39/0.55  fof(f650,plain,(
% 1.39/0.55    k1_xboole_0 = sK0),
% 1.39/0.55    inference(trivial_inequality_removal,[],[f644])).
% 1.39/0.55  fof(f644,plain,(
% 1.39/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.39/0.55    inference(superposition,[],[f612,f634])).
% 1.39/0.55  fof(f634,plain,(
% 1.39/0.55    ( ! [X10] : (k1_xboole_0 = k2_zfmisc_1(X10,k1_xboole_0)) )),
% 1.39/0.55    inference(resolution,[],[f494,f43])).
% 1.39/0.55  fof(f494,plain,(
% 1.39/0.55    ( ! [X8,X7] : (r2_hidden(sK7(X7,X8,sK2(k1_xboole_0,k2_zfmisc_1(X7,X8))),X8) | k1_xboole_0 = k2_zfmisc_1(X7,X8)) )),
% 1.39/0.55    inference(forward_demodulation,[],[f126,f124])).
% 1.39/0.55  fof(f126,plain,(
% 1.39/0.55    ( ! [X8,X7] : (k3_tarski(k1_xboole_0) = k2_zfmisc_1(X7,X8) | r2_hidden(sK7(X7,X8,sK2(k1_xboole_0,k2_zfmisc_1(X7,X8))),X8)) )),
% 1.39/0.55    inference(resolution,[],[f90,f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | r2_hidden(sK7(X0,X1,X3),X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f612,plain,(
% 1.39/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.39/0.55    inference(trivial_inequality_removal,[],[f611])).
% 1.39/0.55  fof(f611,plain,(
% 1.39/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.39/0.55    inference(superposition,[],[f40,f609])).
% 1.39/0.55  fof(f609,plain,(
% 1.39/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f604])).
% 1.39/0.55  fof(f604,plain,(
% 1.39/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.39/0.55    inference(resolution,[],[f602,f160])).
% 1.39/0.55  fof(f160,plain,(
% 1.39/0.55    ( ! [X7] : (r2_hidden(sK2(k1_xboole_0,X7),X7) | k1_xboole_0 = X7) )),
% 1.39/0.55    inference(backward_demodulation,[],[f90,f124])).
% 1.39/0.55  fof(f602,plain,(
% 1.39/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f601,f43])).
% 1.39/0.55  fof(f601,plain,(
% 1.39/0.55    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,sK1)),k1_xboole_0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.39/0.55    inference(duplicate_literal_removal,[],[f600])).
% 1.39/0.55  fof(f600,plain,(
% 1.39/0.55    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK2(k1_xboole_0,sK1)),k1_xboole_0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.39/0.55    inference(superposition,[],[f181,f11])).
% 1.39/0.55  fof(f11,plain,(
% 1.39/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.39/0.55    inference(cnf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,plain,(
% 1.39/0.55    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    inference(negated_conjecture,[],[f6])).
% 1.39/0.55  fof(f6,conjecture,(
% 1.39/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.55  fof(f181,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,sK2(k1_xboole_0,X0)),k2_zfmisc_1(X2,X0)) | ~r2_hidden(X1,X2) | k1_xboole_0 = X0) )),
% 1.39/0.55    inference(backward_demodulation,[],[f122,f124])).
% 1.39/0.55  fof(f122,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (k3_tarski(k1_xboole_0) = X0 | ~r2_hidden(X1,X2) | r2_hidden(k4_tarski(X1,sK2(k1_xboole_0,X0)),k2_zfmisc_1(X2,X0))) )),
% 1.39/0.55    inference(resolution,[],[f90,f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ( ! [X4,X0,X5,X1] : (~r2_hidden(X5,X1) | ~r2_hidden(X4,X0) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 1.39/0.55    inference(equality_resolution,[],[f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.39/0.55    inference(equality_resolution,[],[f29])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.39/0.55    inference(cnf_transformation,[],[f3])).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.39/0.55    inference(inner_rewriting,[],[f10])).
% 1.39/0.55  fof(f10,plain,(
% 1.39/0.55    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f8])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.39/0.55    inference(inner_rewriting,[],[f9])).
% 1.39/0.55  fof(f9,plain,(
% 1.39/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f8])).
% 1.39/0.55  % SZS output end Proof for theBenchmark
% 1.39/0.55  % (11300)------------------------------
% 1.39/0.55  % (11300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (11300)Termination reason: Refutation
% 1.39/0.55  
% 1.39/0.55  % (11300)Memory used [KB]: 6652
% 1.39/0.55  % (11300)Time elapsed: 0.122 s
% 1.39/0.55  % (11300)------------------------------
% 1.39/0.55  % (11300)------------------------------
% 1.39/0.55  % (11304)Refutation not found, incomplete strategy% (11304)------------------------------
% 1.39/0.55  % (11304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (11304)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (11304)Memory used [KB]: 10618
% 1.39/0.55  % (11304)Time elapsed: 0.151 s
% 1.39/0.55  % (11304)------------------------------
% 1.39/0.55  % (11304)------------------------------
% 1.39/0.55  % (11318)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.55  % (11293)Success in time 0.184 s
%------------------------------------------------------------------------------
