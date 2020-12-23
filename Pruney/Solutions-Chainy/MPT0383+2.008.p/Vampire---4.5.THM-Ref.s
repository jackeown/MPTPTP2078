%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:41 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 114 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :   96 ( 352 expanded)
%              Number of equality atoms :   10 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(subsumption_resolution,[],[f50,f49])).

% (7719)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f49,plain,(
    ~ r2_hidden(sK4(sK3),sK0) ),
    inference(subsumption_resolution,[],[f48,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f48,plain,
    ( ~ r2_hidden(sK4(sK3),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f45,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f45,plain,(
    ~ m1_subset_1(sK4(sK3),sK0) ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,
    ( ~ r2_hidden(sK5(sK3),sK1)
    | ~ m1_subset_1(sK4(sK3),sK0) ),
    inference(subsumption_resolution,[],[f38,f22])).

fof(f38,plain,
    ( ~ m1_subset_1(sK4(sK3),sK0)
    | ~ r2_hidden(sK5(sK3),sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f37,f19])).

fof(f37,plain,
    ( ~ m1_subset_1(sK5(sK3),sK1)
    | ~ m1_subset_1(sK4(sK3),sK0) ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK5(sK3),sK1)
    | ~ m1_subset_1(sK4(sK3),sK0) ),
    inference(superposition,[],[f14,f33])).

fof(f33,plain,(
    sK3 = k4_tarski(sK4(sK3),sK5(sK3)) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1))
      | sK3 = k4_tarski(sK4(sK3),sK5(sK3)) ) ),
    inference(resolution,[],[f23,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3,X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f21,f15])).

fof(f15,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f14,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    r2_hidden(sK5(sK3),sK1) ),
    inference(resolution,[],[f42,f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X1,X0))
      | r2_hidden(sK5(sK3),X0) ) ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK5(sK3),X1) ) ),
    inference(superposition,[],[f25,f33])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f50,plain,(
    r2_hidden(sK4(sK3),sK0) ),
    inference(resolution,[],[f43,f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK4(sK3),X0) ) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3,k2_zfmisc_1(X2,X3))
      | r2_hidden(sK4(sK3),X2) ) ),
    inference(superposition,[],[f24,f33])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (7740)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (7732)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (7735)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (7724)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (7728)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (7743)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (7744)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (7735)Refutation not found, incomplete strategy% (7735)------------------------------
% 0.21/0.52  % (7735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (7721)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.52  % (7735)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.52  
% 1.30/0.52  % (7735)Memory used [KB]: 10618
% 1.30/0.52  % (7735)Time elapsed: 0.114 s
% 1.30/0.52  % (7735)------------------------------
% 1.30/0.52  % (7735)------------------------------
% 1.30/0.52  % (7724)Refutation found. Thanks to Tanya!
% 1.30/0.52  % SZS status Theorem for theBenchmark
% 1.30/0.52  % (7730)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.52  % (7722)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.52  % SZS output start Proof for theBenchmark
% 1.30/0.52  fof(f51,plain,(
% 1.30/0.52    $false),
% 1.30/0.52    inference(subsumption_resolution,[],[f50,f49])).
% 1.30/0.52  % (7719)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.53  fof(f49,plain,(
% 1.30/0.53    ~r2_hidden(sK4(sK3),sK0)),
% 1.30/0.53    inference(subsumption_resolution,[],[f48,f22])).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f12])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.30/0.53    inference(ennf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 1.30/0.53  fof(f48,plain,(
% 1.30/0.53    ~r2_hidden(sK4(sK3),sK0) | v1_xboole_0(sK0)),
% 1.30/0.53    inference(resolution,[],[f45,f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f10])).
% 1.30/0.53  fof(f10,plain,(
% 1.30/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f5])).
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.30/0.53  fof(f45,plain,(
% 1.30/0.53    ~m1_subset_1(sK4(sK3),sK0)),
% 1.30/0.53    inference(resolution,[],[f44,f39])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ~r2_hidden(sK5(sK3),sK1) | ~m1_subset_1(sK4(sK3),sK0)),
% 1.30/0.53    inference(subsumption_resolution,[],[f38,f22])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ~m1_subset_1(sK4(sK3),sK0) | ~r2_hidden(sK5(sK3),sK1) | v1_xboole_0(sK1)),
% 1.30/0.53    inference(resolution,[],[f37,f19])).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    ~m1_subset_1(sK5(sK3),sK1) | ~m1_subset_1(sK4(sK3),sK0)),
% 1.30/0.53    inference(trivial_inequality_removal,[],[f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    sK3 != sK3 | ~m1_subset_1(sK5(sK3),sK1) | ~m1_subset_1(sK4(sK3),sK0)),
% 1.30/0.53    inference(superposition,[],[f14,f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    sK3 = k4_tarski(sK4(sK3),sK5(sK3))),
% 1.30/0.53    inference(resolution,[],[f32,f16])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,plain,(
% 1.30/0.53    ? [X0,X1,X2,X3] : (! [X4] : (! [X5] : (k4_tarski(X4,X5) != X3 | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,X0)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 1.30/0.53    inference(ennf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 1.30/0.53    inference(negated_conjecture,[],[f6])).
% 1.30/0.53  fof(f6,conjecture,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ~(! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => k4_tarski(X4,X5) != X3)) & r1_tarski(X2,k2_zfmisc_1(X0,X1)) & r2_hidden(X3,X2))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r1_tarski(sK2,k2_zfmisc_1(X0,X1)) | sK3 = k4_tarski(sK4(sK3),sK5(sK3))) )),
% 1.30/0.53    inference(resolution,[],[f23,f29])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ( ! [X0] : (r2_hidden(sK3,X0) | ~r1_tarski(sK2,X0)) )),
% 1.30/0.53    inference(resolution,[],[f21,f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    r2_hidden(sK3,sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f11])).
% 1.30/0.53  fof(f11,plain,(
% 1.30/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.30/0.53    inference(ennf_transformation,[],[f8])).
% 1.30/0.53  fof(f8,plain,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK4(X0),sK5(X0)) = X0) )),
% 1.30/0.53    inference(cnf_transformation,[],[f13])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 1.30/0.53  fof(f14,plain,(
% 1.30/0.53    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~m1_subset_1(X5,sK1) | ~m1_subset_1(X4,sK0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    r2_hidden(sK5(sK3),sK1)),
% 1.30/0.53    inference(resolution,[],[f42,f16])).
% 1.30/0.53  fof(f42,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r1_tarski(sK2,k2_zfmisc_1(X1,X0)) | r2_hidden(sK5(sK3),X0)) )),
% 1.30/0.53    inference(resolution,[],[f34,f29])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r2_hidden(sK3,k2_zfmisc_1(X0,X1)) | r2_hidden(sK5(sK3),X1)) )),
% 1.30/0.53    inference(superposition,[],[f25,f33])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.30/0.53  fof(f50,plain,(
% 1.30/0.53    r2_hidden(sK4(sK3),sK0)),
% 1.30/0.53    inference(resolution,[],[f43,f16])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r1_tarski(sK2,k2_zfmisc_1(X0,X1)) | r2_hidden(sK4(sK3),X0)) )),
% 1.30/0.53    inference(resolution,[],[f35,f29])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ( ! [X2,X3] : (~r2_hidden(sK3,k2_zfmisc_1(X2,X3)) | r2_hidden(sK4(sK3),X2)) )),
% 1.30/0.53    inference(superposition,[],[f24,f33])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f4])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (7724)------------------------------
% 1.30/0.53  % (7724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (7724)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (7724)Memory used [KB]: 6268
% 1.30/0.53  % (7724)Time elapsed: 0.082 s
% 1.30/0.53  % (7724)------------------------------
% 1.30/0.53  % (7724)------------------------------
% 1.30/0.53  % (7717)Success in time 0.168 s
%------------------------------------------------------------------------------
