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
% DateTime   : Thu Dec  3 12:59:14 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   51 (5411 expanded)
%              Number of leaves         :    4 (1609 expanded)
%              Depth                    :   23
%              Number of atoms          :  128 (13254 expanded)
%              Number of equality atoms :  127 (13253 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(subsumption_resolution,[],[f200,f224])).

% (21198)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f224,plain,(
    ! [X39,X37,X36] :
      ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37)
      | X36 = X39 ) ),
    inference(subsumption_resolution,[],[f223,f175])).

fof(f175,plain,(
    ! [X0] : sK2 = X0 ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X59,X58] :
      ( k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k1_xboole_0,X59)
      | sK2 = X58 ) ),
    inference(superposition,[],[f134,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ),
    inference(subsumption_resolution,[],[f122,f111])).

fof(f111,plain,(
    ! [X0] :
      ( sK0 = sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | sK4 = X0 ) ),
    inference(superposition,[],[f33,f85])).

fof(f85,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5) ),
    inference(unit_resulting_resolution,[],[f29,f68,f33])).

fof(f68,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3) ),
    inference(backward_demodulation,[],[f50,f62])).

fof(f62,plain,(
    sK2 = sK6 ),
    inference(unit_resulting_resolution,[],[f29,f50,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X1 = X4 ) ),
    inference(definition_unfolding,[],[f20,f24,f24,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f50,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3) ),
    inference(backward_demodulation,[],[f30,f44])).

fof(f44,plain,(
    sK3 = sK7 ),
    inference(unit_resulting_resolution,[],[f29,f30,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X2 = X5 ) ),
    inference(definition_unfolding,[],[f21,f24,f24,f24])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7) ),
    inference(definition_unfolding,[],[f17,f28,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f17,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f29,plain,(
    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f18,f28])).

fof(f18,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f19,f24,f24,f24])).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,(
    ! [X0] :
      ( sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f121,f62])).

fof(f121,plain,(
    ! [X0] :
      ( sK2 != sK6
      | sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( sK1 != sK1
      | sK2 != sK6
      | sK0 != sK4
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(superposition,[],[f55,f116])).

fof(f116,plain,(
    ! [X0] :
      ( sK1 = sK5
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X10,X8,X11,X9] :
      ( k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X11)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10)
      | sK5 = X9 ) ),
    inference(superposition,[],[f32,f85])).

fof(f55,plain,
    ( sK1 != sK5
    | sK2 != sK6
    | sK0 != sK4 ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( sK3 != sK3
    | sK1 != sK5
    | sK2 != sK6
    | sK0 != sK4 ),
    inference(superposition,[],[f16,f44])).

fof(f16,plain,
    ( sK3 != sK7
    | sK1 != sK5
    | sK2 != sK6
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f12])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k1_xboole_0,sK3)
      | sK2 = X1 ) ),
    inference(backward_demodulation,[],[f73,f123])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK2 = X1 ) ),
    inference(forward_demodulation,[],[f72,f62])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK6 = X1 ) ),
    inference(subsumption_resolution,[],[f64,f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)
      | sK6 = X1 ) ),
    inference(superposition,[],[f32,f50])).

fof(f223,plain,(
    ! [X39,X37,X36] :
      ( sK2 != k2_zfmisc_1(k1_xboole_0,X37)
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37)
      | X36 = X39 ) ),
    inference(forward_demodulation,[],[f184,f175])).

fof(f184,plain,(
    ! [X39,X37,X36,X40] :
      ( k2_zfmisc_1(k1_xboole_0,X37) != k2_zfmisc_1(sK2,X40)
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37)
      | X36 = X39 ) ),
    inference(backward_demodulation,[],[f153,f175])).

fof(f153,plain,(
    ! [X39,X37,X38,X36,X40] :
      ( k2_zfmisc_1(k2_zfmisc_1(X38,X39),X40) != k2_zfmisc_1(k1_xboole_0,X37)
      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37)
      | X36 = X39 ) ),
    inference(superposition,[],[f32,f123])).

fof(f200,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f130,f175])).

fof(f130,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f29,f123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:35:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21176)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (21178)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (21186)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (21177)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (21180)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (21181)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (21202)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (21202)Refutation not found, incomplete strategy% (21202)------------------------------
% 0.22/0.53  % (21202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21202)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21202)Memory used [KB]: 1663
% 0.22/0.53  % (21202)Time elapsed: 0.114 s
% 0.22/0.53  % (21202)------------------------------
% 0.22/0.53  % (21202)------------------------------
% 0.22/0.53  % (21192)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (21197)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (21184)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (21201)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (21173)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (21195)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (21179)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (21189)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (21188)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (21187)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (21187)Refutation not found, incomplete strategy% (21187)------------------------------
% 0.22/0.54  % (21187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21187)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21187)Memory used [KB]: 1663
% 0.22/0.54  % (21187)Time elapsed: 0.096 s
% 0.22/0.54  % (21187)------------------------------
% 0.22/0.54  % (21187)------------------------------
% 0.22/0.54  % (21200)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (21174)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (21183)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (21190)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (21175)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.55  % (21191)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.31/0.55  % (21182)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.31/0.55  % (21192)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % SZS output start Proof for theBenchmark
% 1.31/0.55  fof(f229,plain,(
% 1.31/0.55    $false),
% 1.31/0.55    inference(subsumption_resolution,[],[f200,f224])).
% 1.31/0.55  % (21198)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.55  fof(f224,plain,(
% 1.31/0.55    ( ! [X39,X37,X36] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37) | X36 = X39) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f223,f175])).
% 1.31/0.55  fof(f175,plain,(
% 1.31/0.55    ( ! [X0] : (sK2 = X0) )),
% 1.31/0.55    inference(equality_resolution,[],[f158])).
% 1.31/0.55  fof(f158,plain,(
% 1.31/0.55    ( ! [X59,X58] : (k2_zfmisc_1(k1_xboole_0,sK3) != k2_zfmisc_1(k1_xboole_0,X59) | sK2 = X58) )),
% 1.31/0.55    inference(superposition,[],[f134,f123])).
% 1.31/0.55  fof(f123,plain,(
% 1.31/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f122,f111])).
% 1.31/0.55  fof(f111,plain,(
% 1.31/0.55    ( ! [X0] : (sK0 = sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.31/0.55    inference(equality_resolution,[],[f96])).
% 1.31/0.55  fof(f96,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | sK4 = X0) )),
% 1.31/0.55    inference(superposition,[],[f33,f85])).
% 1.31/0.55  fof(f85,plain,(
% 1.31/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK4,sK5)),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f29,f68,f33])).
% 1.31/0.55  fof(f68,plain,(
% 1.31/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK2),sK3)),
% 1.31/0.55    inference(backward_demodulation,[],[f50,f62])).
% 1.31/0.55  fof(f62,plain,(
% 1.31/0.55    sK2 = sK6),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f29,f50,f32])).
% 1.31/0.55  fof(f32,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X1 = X4) )),
% 1.31/0.55    inference(definition_unfolding,[],[f20,f24,f24,f24])).
% 1.31/0.55  fof(f24,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f5])).
% 1.31/0.55  fof(f5,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.31/0.55  fof(f20,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X1 = X4) )),
% 1.31/0.55    inference(cnf_transformation,[],[f14])).
% 1.31/0.55  fof(f14,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.31/0.55    inference(flattening,[],[f13])).
% 1.31/0.55  fof(f13,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.31/0.55    inference(ennf_transformation,[],[f8])).
% 1.31/0.55  fof(f8,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 1.31/0.55  fof(f50,plain,(
% 1.31/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK3)),
% 1.31/0.55    inference(backward_demodulation,[],[f30,f44])).
% 1.31/0.55  fof(f44,plain,(
% 1.31/0.55    sK3 = sK7),
% 1.31/0.55    inference(unit_resulting_resolution,[],[f29,f30,f31])).
% 1.31/0.55  fof(f31,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X2 = X5) )),
% 1.31/0.55    inference(definition_unfolding,[],[f21,f24,f24,f24])).
% 1.31/0.55  fof(f21,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X2 = X5) )),
% 1.31/0.55    inference(cnf_transformation,[],[f14])).
% 1.31/0.55  fof(f30,plain,(
% 1.31/0.55    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)),
% 1.31/0.55    inference(definition_unfolding,[],[f17,f28,f28])).
% 1.31/0.55  fof(f28,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.31/0.55    inference(definition_unfolding,[],[f23,f24])).
% 1.31/0.55  fof(f23,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f6])).
% 1.31/0.55  fof(f6,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.31/0.55  fof(f17,plain,(
% 1.31/0.55    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 1.31/0.55    inference(cnf_transformation,[],[f12])).
% 1.31/0.55  fof(f12,plain,(
% 1.31/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.31/0.55    inference(flattening,[],[f11])).
% 1.31/0.55  fof(f11,plain,(
% 1.31/0.55    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 1.31/0.55    inference(ennf_transformation,[],[f10])).
% 1.31/0.55  fof(f10,negated_conjecture,(
% 1.31/0.55    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.55    inference(negated_conjecture,[],[f9])).
% 1.31/0.55  fof(f9,conjecture,(
% 1.31/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_mcart_1)).
% 1.31/0.55  fof(f29,plain,(
% 1.31/0.55    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 1.31/0.55    inference(definition_unfolding,[],[f18,f28])).
% 1.31/0.55  fof(f18,plain,(
% 1.31/0.55    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 1.31/0.55    inference(cnf_transformation,[],[f12])).
% 1.31/0.55  fof(f33,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | X0 = X3) )),
% 1.31/0.55    inference(definition_unfolding,[],[f19,f24,f24,f24])).
% 1.31/0.55  fof(f19,plain,(
% 1.31/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) | X0 = X3) )),
% 1.31/0.55    inference(cnf_transformation,[],[f14])).
% 1.31/0.55  fof(f122,plain,(
% 1.31/0.55    ( ! [X0] : (sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f121,f62])).
% 1.31/0.55  fof(f121,plain,(
% 1.31/0.55    ( ! [X0] : (sK2 != sK6 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.31/0.55    inference(trivial_inequality_removal,[],[f118])).
% 1.31/0.55  fof(f118,plain,(
% 1.31/0.55    ( ! [X0] : (sK1 != sK1 | sK2 != sK6 | sK0 != sK4 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.31/0.55    inference(superposition,[],[f55,f116])).
% 1.31/0.55  fof(f116,plain,(
% 1.31/0.55    ( ! [X0] : (sK1 = sK5 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) )),
% 1.31/0.55    inference(equality_resolution,[],[f98])).
% 1.31/0.55  fof(f98,plain,(
% 1.31/0.55    ( ! [X10,X8,X11,X9] : (k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X11) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10) | sK5 = X9) )),
% 1.31/0.55    inference(superposition,[],[f32,f85])).
% 1.31/0.55  fof(f55,plain,(
% 1.31/0.55    sK1 != sK5 | sK2 != sK6 | sK0 != sK4),
% 1.31/0.55    inference(trivial_inequality_removal,[],[f54])).
% 1.31/0.55  fof(f54,plain,(
% 1.31/0.55    sK3 != sK3 | sK1 != sK5 | sK2 != sK6 | sK0 != sK4),
% 1.31/0.55    inference(superposition,[],[f16,f44])).
% 1.31/0.55  fof(f16,plain,(
% 1.31/0.55    sK3 != sK7 | sK1 != sK5 | sK2 != sK6 | sK0 != sK4),
% 1.31/0.55    inference(cnf_transformation,[],[f12])).
% 1.31/0.55  fof(f134,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k1_xboole_0,sK3) | sK2 = X1) )),
% 1.31/0.55    inference(backward_demodulation,[],[f73,f123])).
% 1.31/0.55  fof(f73,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK2 = X1) )),
% 1.31/0.55    inference(forward_demodulation,[],[f72,f62])).
% 1.31/0.55  fof(f72,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f64,f29])).
% 1.31/0.55  fof(f64,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) | sK6 = X1) )),
% 1.31/0.55    inference(superposition,[],[f32,f50])).
% 1.31/0.55  fof(f223,plain,(
% 1.31/0.55    ( ! [X39,X37,X36] : (sK2 != k2_zfmisc_1(k1_xboole_0,X37) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37) | X36 = X39) )),
% 1.31/0.55    inference(forward_demodulation,[],[f184,f175])).
% 1.31/0.55  fof(f184,plain,(
% 1.31/0.55    ( ! [X39,X37,X36,X40] : (k2_zfmisc_1(k1_xboole_0,X37) != k2_zfmisc_1(sK2,X40) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37) | X36 = X39) )),
% 1.31/0.55    inference(backward_demodulation,[],[f153,f175])).
% 1.31/0.55  fof(f153,plain,(
% 1.31/0.55    ( ! [X39,X37,X38,X36,X40] : (k2_zfmisc_1(k2_zfmisc_1(X38,X39),X40) != k2_zfmisc_1(k1_xboole_0,X37) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X37) | X36 = X39) )),
% 1.31/0.55    inference(superposition,[],[f32,f123])).
% 1.31/0.55  fof(f200,plain,(
% 1.31/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK2)),
% 1.31/0.55    inference(backward_demodulation,[],[f130,f175])).
% 1.31/0.55  fof(f130,plain,(
% 1.31/0.55    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)),
% 1.31/0.55    inference(backward_demodulation,[],[f29,f123])).
% 1.31/0.55  % SZS output end Proof for theBenchmark
% 1.31/0.55  % (21192)------------------------------
% 1.31/0.55  % (21192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (21192)Termination reason: Refutation
% 1.31/0.55  
% 1.31/0.55  % (21192)Memory used [KB]: 1791
% 1.31/0.55  % (21192)Time elapsed: 0.147 s
% 1.31/0.55  % (21192)------------------------------
% 1.31/0.55  % (21192)------------------------------
% 1.31/0.55  % (21185)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.56  % (21191)Refutation not found, incomplete strategy% (21191)------------------------------
% 1.31/0.56  % (21191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (21191)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (21191)Memory used [KB]: 1663
% 1.31/0.56  % (21191)Time elapsed: 0.124 s
% 1.31/0.56  % (21191)------------------------------
% 1.31/0.56  % (21191)------------------------------
% 1.31/0.56  % (21185)Refutation not found, incomplete strategy% (21185)------------------------------
% 1.31/0.56  % (21185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (21185)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.56  
% 1.31/0.56  % (21185)Memory used [KB]: 10618
% 1.31/0.56  % (21185)Time elapsed: 0.154 s
% 1.31/0.56  % (21185)------------------------------
% 1.31/0.56  % (21185)------------------------------
% 1.31/0.56  % (21193)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.56  % (21196)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.57  % (21164)Success in time 0.199 s
%------------------------------------------------------------------------------
