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
% DateTime   : Thu Dec  3 12:42:35 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 179 expanded)
%              Number of leaves         :    5 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  133 ( 544 expanded)
%              Number of equality atoms :   49 ( 319 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(global_subsumption,[],[f72,f277,f303])).

fof(f303,plain,(
    r1_tarski(sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( r1_tarski(sK2,sK0)
    | r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f294,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f294,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK2,X2),sK0)
      | r1_tarski(sK2,X2) ) ),
    inference(resolution,[],[f89,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f89,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK5(sK2,X1),sK4(sK1)),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f80,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(superposition,[],[f62,f12])).

fof(f12,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f62,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(X3,sK4(sK1)),k2_zfmisc_1(X4,sK3))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    r2_hidden(sK4(sK1),sK3) ),
    inference(subsumption_resolution,[],[f47,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK4(sK1),sK3) ),
    inference(subsumption_resolution,[],[f41,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | r2_hidden(sK4(sK1),sK3) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X1,sK3) ) ),
    inference(superposition,[],[f23,f12])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0),sK4(X1)),k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f33,f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,sK4(X2)),k2_zfmisc_1(X1,X2))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f24,f15])).

fof(f277,plain,(
    sK0 != sK2 ),
    inference(trivial_inequality_removal,[],[f276])).

fof(f276,plain,
    ( sK1 != sK1
    | sK0 != sK2 ),
    inference(superposition,[],[f11,f204])).

fof(f204,plain,(
    sK1 = sK3 ),
    inference(resolution,[],[f203,f142])).

fof(f142,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f140,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f140,plain,(
    r1_tarski(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( r1_tarski(sK1,sK3)
    | r1_tarski(sK1,sK3) ),
    inference(resolution,[],[f135,f21])).

fof(f135,plain,(
    ! [X6] :
      ( r2_hidden(sK5(sK1,X6),sK3)
      | r1_tarski(sK1,X6) ) ),
    inference(subsumption_resolution,[],[f129,f13])).

fof(f129,plain,(
    ! [X6] :
      ( r1_tarski(sK1,X6)
      | k1_xboole_0 = sK0
      | r2_hidden(sK5(sK1,X6),sK3) ) ),
    inference(resolution,[],[f37,f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0),sK5(X1,X2)),k2_zfmisc_1(X0,X1))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f34,f15])).

fof(f34,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | r2_hidden(k4_tarski(X3,sK5(X5,X6)),k2_zfmisc_1(X4,X5))
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f24,f20])).

fof(f203,plain,(
    r1_tarski(sK3,sK1) ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( r1_tarski(sK3,sK1)
    | r1_tarski(sK3,sK1) ),
    inference(resolution,[],[f193,f21])).

fof(f193,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK3,X2),sK1)
      | r1_tarski(sK3,X2) ) ),
    inference(resolution,[],[f190,f23])).

fof(f190,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK4(sK0),sK5(sK3,X0)),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(sK3,X0) ) ),
    inference(superposition,[],[f63,f12])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(sK0),sK5(X0,X1)),k2_zfmisc_1(sK2,X0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f50,f34])).

fof(f50,plain,(
    r2_hidden(sK4(sK0),sK2) ),
    inference(subsumption_resolution,[],[f49,f13])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK2) ),
    inference(subsumption_resolution,[],[f42,f14])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0),sK2) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f22,f12])).

fof(f11,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f70,f18])).

fof(f70,plain,(
    r1_tarski(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,
    ( r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f59,f21])).

fof(f59,plain,(
    ! [X7] :
      ( r2_hidden(sK5(sK0,X7),sK2)
      | r1_tarski(sK0,X7) ) ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f54,plain,(
    ! [X7] :
      ( k1_xboole_0 = sK1
      | r1_tarski(sK0,X7)
      | r2_hidden(sK5(sK0,X7),sK2) ) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(k4_tarski(sK5(X2,X3),sK4(X4)),k2_zfmisc_1(X2,X4))
      | k1_xboole_0 = X4
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f33,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.51  % (9029)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.51  % (9045)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.51  % (9027)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.52  % (9035)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (9029)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % (9025)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (9052)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.53  % (9051)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.23/0.53  % (9024)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f304,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(global_subsumption,[],[f72,f277,f303])).
% 0.23/0.53  fof(f303,plain,(
% 0.23/0.53    r1_tarski(sK2,sK0)),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f298])).
% 0.23/0.53  fof(f298,plain,(
% 0.23/0.53    r1_tarski(sK2,sK0) | r1_tarski(sK2,sK0)),
% 0.23/0.53    inference(resolution,[],[f294,f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.23/0.53  fof(f294,plain,(
% 0.23/0.53    ( ! [X2] : (r2_hidden(sK5(sK2,X2),sK0) | r1_tarski(sK2,X2)) )),
% 0.23/0.53    inference(resolution,[],[f89,f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.23/0.53  fof(f89,plain,(
% 0.23/0.53    ( ! [X1] : (r2_hidden(k4_tarski(sK5(sK2,X1),sK4(sK1)),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK2,X1)) )),
% 0.23/0.53    inference(resolution,[],[f80,f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f80,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(k4_tarski(X0,sK4(sK1)),k2_zfmisc_1(sK0,sK1))) )),
% 0.23/0.53    inference(superposition,[],[f62,f12])).
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.23/0.53    inference(flattening,[],[f7])).
% 0.23/0.53  fof(f7,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.53    inference(negated_conjecture,[],[f5])).
% 0.23/0.53  fof(f5,conjecture,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,sK4(sK1)),k2_zfmisc_1(X4,sK3)) | ~r2_hidden(X3,X4)) )),
% 0.23/0.53    inference(resolution,[],[f48,f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    r2_hidden(sK4(sK1),sK3)),
% 0.23/0.53    inference(subsumption_resolution,[],[f47,f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    k1_xboole_0 != sK0),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    k1_xboole_0 = sK0 | r2_hidden(sK4(sK1),sK3)),
% 0.23/0.53    inference(subsumption_resolution,[],[f41,f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    k1_xboole_0 != sK1),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | r2_hidden(sK4(sK1),sK3)),
% 0.23/0.53    inference(resolution,[],[f35,f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,sK3)) )),
% 0.23/0.53    inference(superposition,[],[f23,f12])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0),sK4(X1)),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.23/0.53    inference(resolution,[],[f33,f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,plain,(
% 0.23/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,sK4(X2)),k2_zfmisc_1(X1,X2)) | k1_xboole_0 = X2) )),
% 0.23/0.53    inference(resolution,[],[f24,f15])).
% 0.23/0.53  fof(f277,plain,(
% 0.23/0.53    sK0 != sK2),
% 0.23/0.53    inference(trivial_inequality_removal,[],[f276])).
% 0.23/0.53  fof(f276,plain,(
% 0.23/0.53    sK1 != sK1 | sK0 != sK2),
% 0.23/0.53    inference(superposition,[],[f11,f204])).
% 0.23/0.53  fof(f204,plain,(
% 0.23/0.53    sK1 = sK3),
% 0.23/0.53    inference(resolution,[],[f203,f142])).
% 0.23/0.53  fof(f142,plain,(
% 0.23/0.53    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 0.23/0.53    inference(resolution,[],[f140,f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.53  fof(f140,plain,(
% 0.23/0.53    r1_tarski(sK1,sK3)),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f136])).
% 0.23/0.53  fof(f136,plain,(
% 0.23/0.53    r1_tarski(sK1,sK3) | r1_tarski(sK1,sK3)),
% 0.23/0.53    inference(resolution,[],[f135,f21])).
% 0.23/0.53  fof(f135,plain,(
% 0.23/0.53    ( ! [X6] : (r2_hidden(sK5(sK1,X6),sK3) | r1_tarski(sK1,X6)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f129,f13])).
% 0.23/0.53  fof(f129,plain,(
% 0.23/0.53    ( ! [X6] : (r1_tarski(sK1,X6) | k1_xboole_0 = sK0 | r2_hidden(sK5(sK1,X6),sK3)) )),
% 0.23/0.53    inference(resolution,[],[f37,f32])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0),sK5(X1,X2)),k2_zfmisc_1(X0,X1)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.23/0.53    inference(resolution,[],[f34,f15])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ( ! [X6,X4,X5,X3] : (~r2_hidden(X3,X4) | r2_hidden(k4_tarski(X3,sK5(X5,X6)),k2_zfmisc_1(X4,X5)) | r1_tarski(X5,X6)) )),
% 0.23/0.53    inference(resolution,[],[f24,f20])).
% 0.23/0.53  fof(f203,plain,(
% 0.23/0.53    r1_tarski(sK3,sK1)),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f198])).
% 0.23/0.53  fof(f198,plain,(
% 0.23/0.53    r1_tarski(sK3,sK1) | r1_tarski(sK3,sK1)),
% 0.23/0.53    inference(resolution,[],[f193,f21])).
% 0.23/0.53  fof(f193,plain,(
% 0.23/0.53    ( ! [X2] : (r2_hidden(sK5(sK3,X2),sK1) | r1_tarski(sK3,X2)) )),
% 0.23/0.53    inference(resolution,[],[f190,f23])).
% 0.23/0.53  fof(f190,plain,(
% 0.23/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK4(sK0),sK5(sK3,X0)),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK3,X0)) )),
% 0.23/0.53    inference(superposition,[],[f63,f12])).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(sK0),sK5(X0,X1)),k2_zfmisc_1(sK2,X0)) | r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(resolution,[],[f50,f34])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    r2_hidden(sK4(sK0),sK2)),
% 0.23/0.53    inference(subsumption_resolution,[],[f49,f13])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    k1_xboole_0 = sK0 | r2_hidden(sK4(sK0),sK2)),
% 0.23/0.53    inference(subsumption_resolution,[],[f42,f14])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | r2_hidden(sK4(sK0),sK2)),
% 0.23/0.53    inference(resolution,[],[f35,f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK2)) )),
% 0.23/0.53    inference(superposition,[],[f22,f12])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    sK1 != sK3 | sK0 != sK2),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    ~r1_tarski(sK2,sK0) | sK0 = sK2),
% 0.23/0.53    inference(resolution,[],[f70,f18])).
% 0.23/0.53  fof(f70,plain,(
% 0.23/0.53    r1_tarski(sK0,sK2)),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f66])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    r1_tarski(sK0,sK2) | r1_tarski(sK0,sK2)),
% 0.23/0.53    inference(resolution,[],[f59,f21])).
% 0.23/0.53  fof(f59,plain,(
% 0.23/0.53    ( ! [X7] : (r2_hidden(sK5(sK0,X7),sK2) | r1_tarski(sK0,X7)) )),
% 0.23/0.53    inference(subsumption_resolution,[],[f54,f14])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ( ! [X7] : (k1_xboole_0 = sK1 | r1_tarski(sK0,X7) | r2_hidden(sK5(sK0,X7),sK2)) )),
% 0.23/0.53    inference(resolution,[],[f36,f31])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ( ! [X4,X2,X3] : (r2_hidden(k4_tarski(sK5(X2,X3),sK4(X4)),k2_zfmisc_1(X2,X4)) | k1_xboole_0 = X4 | r1_tarski(X2,X3)) )),
% 0.23/0.53    inference(resolution,[],[f33,f20])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (9029)------------------------------
% 0.23/0.53  % (9029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (9029)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (9029)Memory used [KB]: 6524
% 0.23/0.53  % (9029)Time elapsed: 0.093 s
% 0.23/0.53  % (9029)------------------------------
% 0.23/0.53  % (9029)------------------------------
% 0.23/0.54  % (9022)Success in time 0.165 s
%------------------------------------------------------------------------------
