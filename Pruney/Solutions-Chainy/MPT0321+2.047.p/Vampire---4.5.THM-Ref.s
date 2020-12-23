%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (1444 expanded)
%              Number of leaves         :    4 ( 322 expanded)
%              Depth                    :   34
%              Number of atoms          :  174 (4893 expanded)
%              Number of equality atoms :   70 (2980 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f199,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f193,f14])).

fof(f14,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f193,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(subsumption_resolution,[],[f192,f132])).

fof(f132,plain,(
    sK0 != sK2 ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( sK1 != sK1
    | sK0 != sK2 ),
    inference(superposition,[],[f10,f120])).

fof(f120,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f114,f13])).

fof(f114,plain,
    ( sK1 = sK3
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f112,f14])).

fof(f112,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK1 = sK3 ) ),
    inference(subsumption_resolution,[],[f109,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f109,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK1 = sK3
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f93,f14])).

% (28459)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | sK1 = sK3 ) ),
    inference(resolution,[],[f91,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f17,f11])).

fof(f11,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK1 = sK3 ) ),
    inference(condensation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | sK1 = sK3
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK0)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f54,f17])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f49,f13])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f48,f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f45,f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f27,f14])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f21,f19])).

fof(f21,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X3,sK3) ) ),
    inference(superposition,[],[f18,f11])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK3)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X4,sK2) ) ),
    inference(superposition,[],[f19,f11])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK2)
      | sK1 = sK3 ) ),
    inference(subsumption_resolution,[],[f84,f72])).

fof(f72,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK1,sK3),sK1)
      | sK1 = sK3
      | ~ r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f53,f18])).

% (28462)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X0,sK2)
      | sK1 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | sK1 = sK3 ) ),
    inference(condensation,[],[f51])).

fof(f51,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(k4_tarski(X3,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(k4_tarski(X4,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
      | sK1 = sK3 ) ),
    inference(resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(X5,sK3),X5)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(k4_tarski(X4,sK5(X5,sK3)),k2_zfmisc_1(sK0,sK1))
      | sK3 = X5 ) ),
    inference(resolution,[],[f22,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f84,plain,(
    ! [X0,X1] :
      ( sK1 = sK3
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1,sK3),sK1) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sK1 = sK3
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(sK1,sK3),sK1)
      | sK1 = sK3 ) ),
    inference(resolution,[],[f72,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,sK3),sK1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK5(X0,sK3),X0)
      | sK3 = X0 ) ),
    inference(resolution,[],[f25,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f192,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = sK2 ) ),
    inference(subsumption_resolution,[],[f189,f188])).

fof(f188,plain,(
    r2_hidden(sK5(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f185,f132])).

fof(f185,plain,
    ( r2_hidden(sK5(sK0,sK2),sK0)
    | sK0 = sK2 ),
    inference(factoring,[],[f179])).

fof(f179,plain,(
    ! [X1] :
      ( r2_hidden(sK5(X1,sK2),sK0)
      | sK2 = X1
      | r2_hidden(sK5(X1,sK2),X1) ) ),
    inference(resolution,[],[f169,f17])).

fof(f169,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(subsumption_resolution,[],[f168,f13])).

fof(f168,plain,(
    ! [X2] :
      ( k1_xboole_0 = sK1
      | r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(forward_demodulation,[],[f167,f120])).

fof(f167,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK3
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(forward_demodulation,[],[f32,f120])).

fof(f32,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK3)),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK3
      | r2_hidden(sK5(X2,sK2),X2)
      | sK2 = X2 ) ),
    inference(resolution,[],[f28,f15])).

fof(f28,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK2)
      | r2_hidden(k4_tarski(X3,sK4(sK3)),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f22,f14])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(sK0,sK2),sK0)
      | sK0 = sK2 ) ),
    inference(resolution,[],[f188,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X1,sK2),sK0)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK5(X1,sK2),X1)
      | sK2 = X1 ) ),
    inference(resolution,[],[f23,f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (28453)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.48  % (28458)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.48  % (28461)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.49  % (28466)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (28452)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (28465)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (28449)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (28469)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (28450)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (28451)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (28454)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (28472)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (28457)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28448)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (28446)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (28471)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (28463)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (28455)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (28470)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (28466)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f199,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    k1_xboole_0 = sK1),
% 0.21/0.52    inference(resolution,[],[f193,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f192,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    sK0 != sK2),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    sK1 != sK1 | sK0 != sK2),
% 0.21/0.52    inference(superposition,[],[f10,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    sK1 = sK3),
% 0.21/0.52    inference(subsumption_resolution,[],[f114,f13])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    sK1 = sK3 | k1_xboole_0 = sK1),
% 0.21/0.52    inference(resolution,[],[f112,f14])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK1) | sK1 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK1) | sK1 = sK3 | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(resolution,[],[f93,f14])).
% 0.21/0.52  % (28459)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1) | sK1 = sK3) )),
% 0.21/0.52    inference(resolution,[],[f91,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f20,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) )),
% 0.21/0.52    inference(superposition,[],[f17,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | sK1 = sK3) )),
% 0.21/0.52    inference(condensation,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | sK1 = sK3 | ~r2_hidden(X1,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f85,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(X2,sK0) | ~r2_hidden(X2,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f54,f17])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f13])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK1) )),
% 0.21/0.52    inference(resolution,[],[f48,f14])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f45,f12])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK0) )),
% 0.21/0.52    inference(resolution,[],[f27,f14])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,sK0) | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK1) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))) )),
% 0.21/0.52    inference(resolution,[],[f22,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f21,f19])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X3,sK3)) )),
% 0.21/0.52    inference(superposition,[],[f18,f11])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~r2_hidden(X5,sK3) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X4,sK2)) )),
% 0.21/0.52    inference(superposition,[],[f19,f11])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK2) | sK1 = sK3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(sK5(sK1,sK3),sK1) | sK1 = sK3 | ~r2_hidden(X3,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f53,f18])).
% 0.21/0.52  % (28462)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2) | sK1 = sK3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(k4_tarski(X0,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | sK1 = sK3) )),
% 0.21/0.52    inference(condensation,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X4,X3] : (~r2_hidden(X3,sK2) | r2_hidden(k4_tarski(X3,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X4,sK2) | r2_hidden(k4_tarski(X4,sK5(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | sK1 = sK3) )),
% 0.21/0.52    inference(resolution,[],[f48,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X4,X5] : (r2_hidden(sK5(X5,sK3),X5) | ~r2_hidden(X4,sK2) | r2_hidden(k4_tarski(X4,sK5(X5,sK3)),k2_zfmisc_1(sK0,sK1)) | sK3 = X5) )),
% 0.21/0.52    inference(resolution,[],[f22,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK1 = sK3 | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK0) | ~r2_hidden(sK5(sK1,sK3),sK1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK1 = sK3 | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,sK0) | ~r2_hidden(sK5(sK1,sK3),sK1) | sK1 = sK3) )),
% 0.21/0.52    inference(resolution,[],[f72,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,sK3),sK1) | ~r2_hidden(X1,sK0) | ~r2_hidden(sK5(X0,sK3),X0) | sK3 = X0) )),
% 0.21/0.52    inference(resolution,[],[f25,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    sK1 != sK3 | sK0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = sK2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f189,f188])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    r2_hidden(sK5(sK0,sK2),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f185,f132])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    r2_hidden(sK5(sK0,sK2),sK0) | sK0 = sK2),
% 0.21/0.52    inference(factoring,[],[f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ( ! [X1] : (r2_hidden(sK5(X1,sK2),sK0) | sK2 = X1 | r2_hidden(sK5(X1,sK2),X1)) )),
% 0.21/0.52    inference(resolution,[],[f169,f17])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK5(X2,sK2),X2) | sK2 = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f168,f13])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ( ! [X2] : (k1_xboole_0 = sK1 | r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK5(X2,sK2),X2) | sK2 = X2) )),
% 0.21/0.52    inference(forward_demodulation,[],[f167,f120])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK1)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3 | r2_hidden(sK5(X2,sK2),X2) | sK2 = X2) )),
% 0.21/0.52    inference(forward_demodulation,[],[f32,f120])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X2] : (r2_hidden(k4_tarski(sK5(X2,sK2),sK4(sK3)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3 | r2_hidden(sK5(X2,sK2),X2) | sK2 = X2) )),
% 0.21/0.52    inference(resolution,[],[f28,f15])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(k4_tarski(X3,sK4(sK3)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3) )),
% 0.21/0.52    inference(resolution,[],[f22,f14])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(sK5(sK0,sK2),sK0) | sK0 = sK2) )),
% 0.21/0.52    inference(resolution,[],[f188,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK5(X1,sK2),sK0) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK5(X1,sK2),X1) | sK2 = X1) )),
% 0.21/0.52    inference(resolution,[],[f23,f16])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28466)------------------------------
% 0.21/0.52  % (28466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28466)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28466)Memory used [KB]: 1791
% 0.21/0.52  % (28466)Time elapsed: 0.102 s
% 0.21/0.52  % (28466)------------------------------
% 0.21/0.52  % (28466)------------------------------
% 0.21/0.52  % (28444)Success in time 0.154 s
%------------------------------------------------------------------------------
