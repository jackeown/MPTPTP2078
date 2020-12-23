%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:15 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 405 expanded)
%              Number of leaves         :    9 ( 118 expanded)
%              Depth                    :   22
%              Number of atoms          :  136 ( 749 expanded)
%              Number of equality atoms :   90 ( 596 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(subsumption_resolution,[],[f401,f322])).

fof(f322,plain,(
    k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f17,f321])).

fof(f321,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f320,f79])).

fof(f79,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f43,f38])).

fof(f38,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1) ),
    inference(definition_unfolding,[],[f16,f37,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

% (5669)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f320,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f291,f47])).

% (5671)Refutation not found, incomplete strategy% (5671)------------------------------
% (5671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5671)Termination reason: Refutation not found, incomplete strategy

% (5671)Memory used [KB]: 10618
% (5671)Time elapsed: 0.140 s
% (5671)------------------------------
% (5671)------------------------------
fof(f47,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f291,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f38,f285])).

fof(f285,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f280,f79])).

fof(f280,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    inference(resolution,[],[f279,f152])).

fof(f152,plain,
    ( r1_tarski(sK0,sK1)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    inference(resolution,[],[f75,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(k2_zfmisc_1(X19,X20),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0))
      | k1_xboole_0 = k2_zfmisc_1(X19,X20)
      | r1_tarski(X20,sK1) ) ),
    inference(superposition,[],[f31,f38])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k2_zfmisc_1(X0,X1) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f279,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f277,f17])).

fof(f277,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f254,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f254,plain,
    ( r1_tarski(sK1,sK0)
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f252,f31])).

fof(f252,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f247,f79])).

fof(f247,plain,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    inference(resolution,[],[f224,f152])).

fof(f224,plain,
    ( ~ r1_tarski(sK0,sK1)
    | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f66,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f66,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),k2_zfmisc_1(X5,sK1))
      | k1_xboole_0 = sK1
      | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),X5) ) ),
    inference(superposition,[],[f27,f38])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f17,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f401,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f400])).

fof(f400,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f43,f356])).

fof(f356,plain,(
    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) ),
    inference(forward_demodulation,[],[f323,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f323,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f38,f321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 15:37:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.49  % (5660)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.18/0.49  % (5678)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.18/0.49  % (5660)Refutation not found, incomplete strategy% (5660)------------------------------
% 0.18/0.49  % (5660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (5668)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.18/0.49  % (5660)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (5660)Memory used [KB]: 1663
% 0.18/0.49  % (5660)Time elapsed: 0.095 s
% 0.18/0.49  % (5660)------------------------------
% 0.18/0.49  % (5660)------------------------------
% 0.18/0.50  % (5663)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.18/0.50  % (5665)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.51  % (5659)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.18/0.51  % (5676)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.18/0.51  % (5666)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.18/0.52  % (5683)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.18/0.52  % (5661)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.18/0.52  % (5676)Refutation found. Thanks to Tanya!
% 0.18/0.52  % SZS status Theorem for theBenchmark
% 0.18/0.52  % (5687)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.18/0.52  % (5662)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.18/0.52  % (5673)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.52  % (5673)Refutation not found, incomplete strategy% (5673)------------------------------
% 0.18/0.52  % (5673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (5688)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.52  % (5688)Refutation not found, incomplete strategy% (5688)------------------------------
% 0.18/0.52  % (5688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (5688)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (5688)Memory used [KB]: 1663
% 0.18/0.52  % (5688)Time elapsed: 0.094 s
% 0.18/0.52  % (5688)------------------------------
% 0.18/0.52  % (5688)------------------------------
% 0.18/0.52  % (5671)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.18/0.52  % (5684)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.18/0.53  % (5674)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.18/0.53  % (5663)Refutation not found, incomplete strategy% (5663)------------------------------
% 0.18/0.53  % (5663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (5663)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (5663)Memory used [KB]: 1791
% 0.18/0.53  % (5663)Time elapsed: 0.137 s
% 0.18/0.53  % (5663)------------------------------
% 0.18/0.53  % (5663)------------------------------
% 0.18/0.53  % (5673)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (5673)Memory used [KB]: 1663
% 0.18/0.53  % (5673)Time elapsed: 0.127 s
% 0.18/0.53  % (5673)------------------------------
% 0.18/0.53  % (5673)------------------------------
% 0.18/0.53  % (5675)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.18/0.53  % (5675)Refutation not found, incomplete strategy% (5675)------------------------------
% 0.18/0.53  % (5675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (5675)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (5675)Memory used [KB]: 10618
% 0.18/0.53  % (5675)Time elapsed: 0.140 s
% 0.18/0.53  % (5675)------------------------------
% 0.18/0.53  % (5675)------------------------------
% 0.18/0.53  % (5672)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.18/0.53  % (5670)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.18/0.53  % (5664)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.53  % SZS output start Proof for theBenchmark
% 0.18/0.53  fof(f405,plain,(
% 0.18/0.53    $false),
% 0.18/0.53    inference(subsumption_resolution,[],[f401,f322])).
% 0.18/0.53  fof(f322,plain,(
% 0.18/0.53    k1_xboole_0 != sK0),
% 0.18/0.53    inference(backward_demodulation,[],[f17,f321])).
% 0.18/0.53  fof(f321,plain,(
% 0.18/0.53    k1_xboole_0 = sK1),
% 0.18/0.53    inference(subsumption_resolution,[],[f320,f79])).
% 0.18/0.53  fof(f79,plain,(
% 0.18/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1),
% 0.18/0.53    inference(duplicate_literal_removal,[],[f60])).
% 0.18/0.53  fof(f60,plain,(
% 0.18/0.53    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.18/0.53    inference(superposition,[],[f43,f38])).
% 0.18/0.53  fof(f38,plain,(
% 0.18/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),sK1)),
% 0.18/0.53    inference(definition_unfolding,[],[f16,f37,f37])).
% 0.18/0.53  fof(f37,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.18/0.53    inference(definition_unfolding,[],[f29,f24])).
% 0.18/0.53  fof(f24,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f6])).
% 0.18/0.53  % (5669)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.18/0.53  fof(f6,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.18/0.53  fof(f29,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f7])).
% 0.18/0.53  fof(f7,axiom,(
% 0.18/0.53    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.18/0.53  fof(f16,plain,(
% 0.18/0.53    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 0.18/0.53    inference(cnf_transformation,[],[f11])).
% 0.18/0.53  fof(f11,plain,(
% 0.18/0.53    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 0.18/0.53    inference(ennf_transformation,[],[f10])).
% 0.18/0.53  fof(f10,negated_conjecture,(
% 0.18/0.53    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.18/0.53    inference(negated_conjecture,[],[f9])).
% 0.18/0.53  fof(f9,conjecture,(
% 0.18/0.53    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).
% 0.18/0.53  fof(f43,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.18/0.53    inference(definition_unfolding,[],[f32,f37])).
% 0.18/0.53  fof(f32,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3) )),
% 0.18/0.53    inference(cnf_transformation,[],[f8])).
% 0.18/0.53  fof(f8,axiom,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.18/0.53  fof(f320,plain,(
% 0.18/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) | k1_xboole_0 = sK1),
% 0.18/0.53    inference(forward_demodulation,[],[f291,f47])).
% 0.18/0.53  % (5671)Refutation not found, incomplete strategy% (5671)------------------------------
% 0.18/0.53  % (5671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (5671)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.53  
% 0.18/0.53  % (5671)Memory used [KB]: 10618
% 0.18/0.53  % (5671)Time elapsed: 0.140 s
% 0.18/0.53  % (5671)------------------------------
% 0.18/0.53  % (5671)------------------------------
% 0.18/0.53  fof(f47,plain,(
% 0.18/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.18/0.53    inference(equality_resolution,[],[f22])).
% 0.18/0.53  fof(f22,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f2])).
% 0.18/0.53  fof(f2,axiom,(
% 0.18/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.53  fof(f291,plain,(
% 0.18/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k1_xboole_0,sK1) | k1_xboole_0 = sK1),
% 0.18/0.53    inference(superposition,[],[f38,f285])).
% 0.18/0.53  fof(f285,plain,(
% 0.18/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.18/0.53    inference(subsumption_resolution,[],[f280,f79])).
% 0.18/0.53  fof(f280,plain,(
% 0.18/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 0.18/0.53    inference(resolution,[],[f279,f152])).
% 0.18/0.53  fof(f152,plain,(
% 0.18/0.53    r1_tarski(sK0,sK1) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 0.18/0.53    inference(resolution,[],[f75,f45])).
% 0.18/0.53  fof(f45,plain,(
% 0.18/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.18/0.53    inference(equality_resolution,[],[f18])).
% 0.18/0.53  fof(f18,plain,(
% 0.18/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.18/0.53    inference(cnf_transformation,[],[f1])).
% 0.18/0.53  fof(f1,axiom,(
% 0.18/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.53  fof(f75,plain,(
% 0.18/0.53    ( ! [X19,X20] : (~r1_tarski(k2_zfmisc_1(X19,X20),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)) | k1_xboole_0 = k2_zfmisc_1(X19,X20) | r1_tarski(X20,sK1)) )),
% 0.18/0.53    inference(superposition,[],[f31,f38])).
% 0.18/0.53  fof(f31,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | r1_tarski(X1,X3)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f15])).
% 0.18/0.53  fof(f15,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.18/0.53    inference(flattening,[],[f14])).
% 0.18/0.53  fof(f14,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.18/0.53    inference(ennf_transformation,[],[f5])).
% 0.18/0.53  fof(f5,axiom,(
% 0.18/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k2_zfmisc_1(X0,X1) = k1_xboole_0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.18/0.53  fof(f279,plain,(
% 0.18/0.53    ~r1_tarski(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.18/0.53    inference(subsumption_resolution,[],[f277,f17])).
% 0.18/0.53  fof(f277,plain,(
% 0.18/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1 | ~r1_tarski(sK0,sK1) | sK0 = sK1),
% 0.18/0.53    inference(resolution,[],[f254,f20])).
% 0.18/0.53  fof(f20,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.18/0.53    inference(cnf_transformation,[],[f1])).
% 0.18/0.53  fof(f254,plain,(
% 0.18/0.53    r1_tarski(sK1,sK0) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.18/0.53    inference(resolution,[],[f252,f31])).
% 0.18/0.53  fof(f252,plain,(
% 0.18/0.53    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) | k1_xboole_0 = sK1),
% 0.18/0.53    inference(subsumption_resolution,[],[f247,f79])).
% 0.18/0.53  fof(f247,plain,(
% 0.18/0.53    r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 0.18/0.53    inference(resolution,[],[f224,f152])).
% 0.18/0.53  fof(f224,plain,(
% 0.18/0.53    ~r1_tarski(sK0,sK1) | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) | k1_xboole_0 = sK1),
% 0.18/0.53    inference(resolution,[],[f66,f26])).
% 0.18/0.53  fof(f26,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f12])).
% 0.18/0.53  fof(f12,plain,(
% 0.18/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.18/0.53    inference(ennf_transformation,[],[f4])).
% 0.18/0.53  fof(f4,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.18/0.53  fof(f66,plain,(
% 0.18/0.53    ( ! [X5] : (~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0),k2_zfmisc_1(X5,sK1)) | k1_xboole_0 = sK1 | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1),X5)) )),
% 0.18/0.53    inference(superposition,[],[f27,f38])).
% 0.18/0.53  fof(f27,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f13])).
% 0.18/0.53  fof(f13,plain,(
% 0.18/0.53    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.18/0.53    inference(ennf_transformation,[],[f3])).
% 0.18/0.53  fof(f3,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.18/0.53  fof(f17,plain,(
% 0.18/0.53    sK0 != sK1),
% 0.18/0.53    inference(cnf_transformation,[],[f11])).
% 0.18/0.53  fof(f401,plain,(
% 0.18/0.53    k1_xboole_0 = sK0),
% 0.18/0.53    inference(trivial_inequality_removal,[],[f400])).
% 0.18/0.53  fof(f400,plain,(
% 0.18/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.18/0.53    inference(duplicate_literal_removal,[],[f382])).
% 0.18/0.53  fof(f382,plain,(
% 0.18/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.18/0.53    inference(superposition,[],[f43,f356])).
% 0.18/0.53  fof(f356,plain,(
% 0.18/0.53    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0)),
% 0.18/0.53    inference(forward_demodulation,[],[f323,f46])).
% 0.18/0.53  fof(f46,plain,(
% 0.18/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.18/0.53    inference(equality_resolution,[],[f23])).
% 0.18/0.53  fof(f23,plain,(
% 0.18/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f2])).
% 0.18/0.53  fof(f323,plain,(
% 0.18/0.53    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0)),
% 0.18/0.53    inference(backward_demodulation,[],[f38,f321])).
% 0.18/0.53  % SZS output end Proof for theBenchmark
% 0.18/0.53  % (5676)------------------------------
% 0.18/0.53  % (5676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (5676)Termination reason: Refutation
% 0.18/0.53  
% 0.18/0.53  % (5676)Memory used [KB]: 1918
% 0.18/0.53  % (5676)Time elapsed: 0.116 s
% 0.18/0.53  % (5676)------------------------------
% 0.18/0.53  % (5676)------------------------------
% 0.18/0.54  % (5658)Success in time 0.195 s
%------------------------------------------------------------------------------
