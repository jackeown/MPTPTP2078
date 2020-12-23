%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:16 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 313 expanded)
%              Number of leaves         :    5 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :   76 ( 543 expanded)
%              Number of equality atoms :   28 ( 282 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f74,f34,f73,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f73,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1))) ),
    inference(subsumption_resolution,[],[f72,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f72,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f69,f68])).

fof(f68,plain,(
    sK1 = sK3 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( sK1 = sK3
    | sK1 = sK3 ),
    inference(resolution,[],[f56,f25])).

fof(f25,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))
    | sK1 = sK3 ),
    inference(definition_unfolding,[],[f15,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,k1_enumset1(X1,X1,X1)))
      | X0 = X1 ) ),
    inference(resolution,[],[f53,f34])).

fof(f53,plain,(
    ! [X6,X4,X8,X7,X5,X3] :
      ( ~ r2_hidden(X5,k1_enumset1(X6,X6,X6))
      | X3 = X4
      | ~ r2_hidden(k4_tarski(X7,X3),k2_zfmisc_1(X8,k1_enumset1(X4,X4,X4))) ) ),
    inference(resolution,[],[f39,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X2,X2,X2))
      | X1 = X2
      | ~ r2_hidden(X3,k1_enumset1(X4,X4,X4)) ) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f17,f24,f24])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f69,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1)))
    | sK1 != sK3
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f27,f68])).

fof(f27,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f13,f24])).

fof(f13,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] : r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f32,f19])).

fof(f32,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3))) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( X1 != X3
      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3))) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f18,f24,f24])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f70,f73])).

fof(f70,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1)))
    | r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f26,f68])).

fof(f26,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f14,f24])).

fof(f14,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:55:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.50  % (30808)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (30814)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (30815)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (30813)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (30807)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (30829)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (30821)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.52  % (30823)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.52  % (30821)Refutation not found, incomplete strategy% (30821)------------------------------
% 1.30/0.52  % (30821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (30821)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.52  
% 1.30/0.52  % (30821)Memory used [KB]: 1663
% 1.30/0.52  % (30821)Time elapsed: 0.125 s
% 1.30/0.52  % (30821)------------------------------
% 1.30/0.52  % (30821)------------------------------
% 1.30/0.52  % (30804)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.52  % (30823)Refutation found. Thanks to Tanya!
% 1.30/0.52  % SZS status Theorem for theBenchmark
% 1.30/0.52  % (30806)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.52  % (30833)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.52  % (30832)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.52  % (30819)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.52  % (30827)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.52  % (30810)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.52  % (30814)Refutation not found, incomplete strategy% (30814)------------------------------
% 1.30/0.52  % (30814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.52  % (30814)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.52  
% 1.30/0.52  % (30814)Memory used [KB]: 10746
% 1.30/0.52  % (30814)Time elapsed: 0.114 s
% 1.30/0.52  % (30814)------------------------------
% 1.30/0.52  % (30814)------------------------------
% 1.30/0.53  % (30832)Refutation not found, incomplete strategy% (30832)------------------------------
% 1.30/0.53  % (30832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (30832)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (30832)Memory used [KB]: 10746
% 1.30/0.53  % (30832)Time elapsed: 0.128 s
% 1.30/0.53  % (30832)------------------------------
% 1.30/0.53  % (30832)------------------------------
% 1.30/0.53  % (30805)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.53  % (30831)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f83,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(unit_resulting_resolution,[],[f74,f34,f73,f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f8])).
% 1.30/0.53  fof(f8,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.30/0.53  fof(f73,plain,(
% 1.30/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1)))),
% 1.30/0.53    inference(subsumption_resolution,[],[f72,f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f8])).
% 1.30/0.53  fof(f72,plain,(
% 1.30/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1))) | ~r2_hidden(sK0,sK2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f69,f68])).
% 1.30/0.53  fof(f68,plain,(
% 1.30/0.53    sK1 = sK3),
% 1.30/0.53    inference(duplicate_literal_removal,[],[f63])).
% 1.30/0.53  fof(f63,plain,(
% 1.30/0.53    sK1 = sK3 | sK1 = sK3),
% 1.30/0.53    inference(resolution,[],[f56,f25])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3))) | sK1 = sK3),
% 1.30/0.53    inference(definition_unfolding,[],[f15,f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.30/0.53    inference(definition_unfolding,[],[f22,f23])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 1.30/0.53    inference(cnf_transformation,[],[f12])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f11])).
% 1.30/0.53  fof(f11,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.30/0.53    inference(negated_conjecture,[],[f10])).
% 1.30/0.53  fof(f10,conjecture,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 1.30/0.53  fof(f56,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,k1_enumset1(X1,X1,X1))) | X0 = X1) )),
% 1.30/0.53    inference(resolution,[],[f53,f34])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    ( ! [X6,X4,X8,X7,X5,X3] : (~r2_hidden(X5,k1_enumset1(X6,X6,X6)) | X3 = X4 | ~r2_hidden(k4_tarski(X7,X3),k2_zfmisc_1(X8,k1_enumset1(X4,X4,X4)))) )),
% 1.30/0.53    inference(resolution,[],[f39,f20])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f8])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ( ! [X4,X2,X3,X1] : (~r2_hidden(X1,k1_enumset1(X2,X2,X2)) | X1 = X2 | ~r2_hidden(X3,k1_enumset1(X4,X4,X4))) )),
% 1.30/0.53    inference(resolution,[],[f29,f21])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3))) | X1 = X3) )),
% 1.30/0.53    inference(definition_unfolding,[],[f17,f24,f24])).
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f9,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 1.30/0.53  fof(f69,plain,(
% 1.30/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1))) | sK1 != sK3 | ~r2_hidden(sK0,sK2)),
% 1.30/0.53    inference(backward_demodulation,[],[f27,f68])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))),
% 1.30/0.53    inference(definition_unfolding,[],[f13,f24])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ~r2_hidden(sK0,sK2) | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 1.30/0.53    inference(cnf_transformation,[],[f12])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ( ! [X0] : (r2_hidden(X0,k1_enumset1(X0,X0,X0))) )),
% 1.30/0.53    inference(unit_resulting_resolution,[],[f32,f19])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3)))) )),
% 1.30/0.53    inference(equality_resolution,[],[f31])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ( ! [X2,X3,X1] : (X1 != X3 | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3)))) )),
% 1.30/0.53    inference(equality_resolution,[],[f28])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_enumset1(X2,X2,X2),k1_enumset1(X3,X3,X3)))) )),
% 1.30/0.53    inference(definition_unfolding,[],[f18,f24,f24])).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f9])).
% 1.30/0.53  fof(f74,plain,(
% 1.30/0.53    r2_hidden(sK0,sK2)),
% 1.30/0.53    inference(subsumption_resolution,[],[f70,f73])).
% 1.30/0.53  fof(f70,plain,(
% 1.30/0.53    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK1,sK1,sK1))) | r2_hidden(sK0,sK2)),
% 1.30/0.53    inference(backward_demodulation,[],[f26,f68])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_enumset1(sK3,sK3,sK3)))),
% 1.30/0.53    inference(definition_unfolding,[],[f14,f24])).
% 1.30/0.53  fof(f14,plain,(
% 1.30/0.53    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 1.30/0.53    inference(cnf_transformation,[],[f12])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (30823)------------------------------
% 1.30/0.53  % (30823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (30823)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (30823)Memory used [KB]: 1791
% 1.30/0.53  % (30823)Time elapsed: 0.134 s
% 1.30/0.53  % (30823)------------------------------
% 1.30/0.53  % (30823)------------------------------
% 1.30/0.53  % (30816)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.53  % (30818)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.53  % (30803)Success in time 0.18 s
%------------------------------------------------------------------------------
