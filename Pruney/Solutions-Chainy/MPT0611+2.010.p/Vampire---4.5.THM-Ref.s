%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:35 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 135 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(subsumption_resolution,[],[f172,f18])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

fof(f172,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f167,f91])).

fof(f91,plain,(
    ! [X0] : r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f90,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f82,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,k2_relat_1(sK0)))
      | r1_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(sK1))) ) ),
    inference(superposition,[],[f28,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1))) ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,(
    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1)) ) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f167,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))
      | r1_xboole_0(X2,sK1) ) ),
    inference(superposition,[],[f24,f163])).

fof(f163,plain,(
    k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f36,f16])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (13515)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (13506)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (13502)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (13512)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (13503)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (13503)Refutation not found, incomplete strategy% (13503)------------------------------
% 0.22/0.51  % (13503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13503)Memory used [KB]: 10490
% 0.22/0.51  % (13503)Time elapsed: 0.102 s
% 0.22/0.51  % (13503)------------------------------
% 0.22/0.51  % (13503)------------------------------
% 0.22/0.51  % (13505)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (13523)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.20/0.51  % (13513)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.20/0.52  % (13504)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.20/0.52  % (13511)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.20/0.52  % (13514)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.20/0.52  % (13524)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.20/0.52  % (13501)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.20/0.52  % (13513)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f173,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f172,f18])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ~r1_xboole_0(sK0,sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.20/0.52    inference(flattening,[],[f9])).
% 1.20/0.52  fof(f9,plain,(
% 1.20/0.52    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f8])).
% 1.20/0.52  fof(f8,negated_conjecture,(
% 1.20/0.52    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.20/0.52    inference(negated_conjecture,[],[f7])).
% 1.20/0.52  fof(f7,conjecture,(
% 1.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).
% 1.20/0.52  fof(f172,plain,(
% 1.20/0.52    r1_xboole_0(sK0,sK1)),
% 1.20/0.52    inference(resolution,[],[f167,f91])).
% 1.20/0.52  fof(f91,plain,(
% 1.20/0.52    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1)))) )),
% 1.20/0.52    inference(subsumption_resolution,[],[f90,f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    v1_relat_1(sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f90,plain,(
% 1.20/0.52    ( ! [X0] : (r1_xboole_0(sK0,k2_zfmisc_1(X0,k2_relat_1(sK1))) | ~v1_relat_1(sK0)) )),
% 1.20/0.52    inference(resolution,[],[f82,f20])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f11,plain,(
% 1.20/0.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.20/0.52    inference(ennf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.20/0.52  fof(f82,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,k2_relat_1(sK0))) | r1_xboole_0(X2,k2_zfmisc_1(X1,k2_relat_1(sK1)))) )),
% 1.20/0.52    inference(superposition,[],[f28,f50])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,k2_relat_1(sK0)) = k4_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK0)),k2_zfmisc_1(X1,k2_relat_1(sK1)))) )),
% 1.20/0.52    inference(resolution,[],[f38,f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    r1_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | k2_zfmisc_1(X2,X0) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) )),
% 1.20/0.52    inference(resolution,[],[f30,f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f15])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 1.20/0.52    inference(ennf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f14])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.20/0.52    inference(ennf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.20/0.52  fof(f167,plain,(
% 1.20/0.52    ( ! [X2] : (~r1_xboole_0(X2,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) | r1_xboole_0(X2,sK1)) )),
% 1.20/0.52    inference(superposition,[],[f24,f163])).
% 1.20/0.52  fof(f163,plain,(
% 1.20/0.52    k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)) = k2_xboole_0(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 1.20/0.52    inference(resolution,[],[f36,f16])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    v1_relat_1(sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)) = k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.20/0.52    inference(resolution,[],[f20,f21])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f12])).
% 1.20/0.52  fof(f12,plain,(
% 1.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.20/0.52  fof(f24,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.20/0.52    inference(ennf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (13513)------------------------------
% 1.20/0.52  % (13513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (13513)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (13513)Memory used [KB]: 6396
% 1.20/0.52  % (13513)Time elapsed: 0.106 s
% 1.20/0.52  % (13513)------------------------------
% 1.20/0.52  % (13513)------------------------------
% 1.20/0.52  % (13524)Refutation not found, incomplete strategy% (13524)------------------------------
% 1.20/0.52  % (13524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (13524)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (13524)Memory used [KB]: 10618
% 1.20/0.52  % (13524)Time elapsed: 0.098 s
% 1.20/0.52  % (13524)------------------------------
% 1.20/0.52  % (13524)------------------------------
% 1.20/0.52  % (13499)Success in time 0.16 s
%------------------------------------------------------------------------------
