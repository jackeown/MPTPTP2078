%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 162 expanded)
%              Number of leaves         :   11 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  108 ( 300 expanded)
%              Number of equality atoms :   70 ( 252 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f881,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f879])).

fof(f879,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f23,f591])).

fof(f591,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f584,f546])).

fof(f546,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f24,f37,f176])).

fof(f176,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X2
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f56,f53])).

fof(f53,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f26,f52,f52])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f584,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f544,f546])).

fof(f544,plain,(
    sK2 = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f503,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f503,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f494,f53])).

fof(f494,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2) ),
    inference(backward_demodulation,[],[f165,f482])).

fof(f482,plain,(
    sK0 = sK3(sK2) ),
    inference(unit_resulting_resolution,[],[f167,f183])).

fof(f183,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_xboole_0(sK1,sK2))
      | sK0 = X3 ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_xboole_0(sK1,sK2))
      | sK0 = X3
      | sK0 = X3
      | sK0 = X3 ) ),
    inference(superposition,[],[f78,f53])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f167,plain,(
    ! [X0] : r2_hidden(sK3(sK2),k2_xboole_0(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f125,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f125,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f25,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f165,plain,(
    r1_tarski(k2_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f125,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f52])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:33:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.40  ipcrm: permission denied for id (1207959576)
% 0.22/0.40  ipcrm: permission denied for id (1207992347)
% 0.22/0.41  ipcrm: permission denied for id (1208057886)
% 0.22/0.42  ipcrm: permission denied for id (1208123433)
% 0.22/0.43  ipcrm: permission denied for id (1208188974)
% 0.22/0.44  ipcrm: permission denied for id (1208320054)
% 0.22/0.44  ipcrm: permission denied for id (1208385594)
% 0.22/0.45  ipcrm: permission denied for id (1208418365)
% 0.22/0.45  ipcrm: permission denied for id (1208451136)
% 0.22/0.46  ipcrm: permission denied for id (1208516676)
% 0.22/0.46  ipcrm: permission denied for id (1208680523)
% 0.22/0.47  ipcrm: permission denied for id (1208713294)
% 0.22/0.47  ipcrm: permission denied for id (1208746065)
% 0.22/0.47  ipcrm: permission denied for id (1208778834)
% 0.22/0.50  ipcrm: permission denied for id (1208811623)
% 0.22/0.51  ipcrm: permission denied for id (1208942703)
% 0.36/0.53  ipcrm: permission denied for id (1209172094)
% 0.39/0.63  % (21642)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.39/0.65  % (21650)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.66  % (21659)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.39/0.68  % (21642)Refutation found. Thanks to Tanya!
% 0.39/0.68  % SZS status Theorem for theBenchmark
% 0.39/0.68  % SZS output start Proof for theBenchmark
% 0.39/0.68  fof(f881,plain,(
% 0.39/0.68    $false),
% 0.39/0.68    inference(trivial_inequality_removal,[],[f879])).
% 0.39/0.68  fof(f879,plain,(
% 0.39/0.68    sK1 != sK1),
% 0.39/0.68    inference(superposition,[],[f23,f591])).
% 0.39/0.68  fof(f591,plain,(
% 0.39/0.68    sK1 = sK2),
% 0.39/0.68    inference(forward_demodulation,[],[f584,f546])).
% 0.39/0.68  fof(f546,plain,(
% 0.39/0.68    sK1 = k2_xboole_0(sK1,sK2)),
% 0.39/0.68    inference(unit_resulting_resolution,[],[f24,f37,f176])).
% 0.39/0.68  fof(f176,plain,(
% 0.39/0.68    ( ! [X2] : (~r1_tarski(X2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X2 | k1_xboole_0 = X2) )),
% 0.39/0.68    inference(superposition,[],[f56,f53])).
% 0.39/0.68  fof(f53,plain,(
% 0.39/0.68    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.39/0.68    inference(definition_unfolding,[],[f22,f52])).
% 0.39/0.68  fof(f52,plain,(
% 0.39/0.68    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.39/0.68    inference(definition_unfolding,[],[f40,f51])).
% 0.39/0.68  fof(f51,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.39/0.68    inference(definition_unfolding,[],[f49,f50])).
% 0.39/0.68  fof(f50,plain,(
% 0.39/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f8])).
% 0.39/0.68  fof(f8,axiom,(
% 0.39/0.68    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.39/0.68  fof(f49,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f7])).
% 0.39/0.68  fof(f7,axiom,(
% 0.39/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.39/0.68  fof(f40,plain,(
% 0.39/0.68    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f6])).
% 0.39/0.68  fof(f6,axiom,(
% 0.39/0.68    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.39/0.68  fof(f22,plain,(
% 0.39/0.68    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.39/0.68    inference(cnf_transformation,[],[f18])).
% 0.39/0.68  fof(f18,plain,(
% 0.39/0.68    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.39/0.68    inference(ennf_transformation,[],[f17])).
% 0.39/0.68  fof(f17,negated_conjecture,(
% 0.39/0.68    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.39/0.68    inference(negated_conjecture,[],[f16])).
% 0.39/0.68  fof(f16,conjecture,(
% 0.39/0.68    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.39/0.68  fof(f56,plain,(
% 0.39/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.39/0.68    inference(definition_unfolding,[],[f26,f52,f52])).
% 0.39/0.68  fof(f26,plain,(
% 0.39/0.68    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f14])).
% 0.39/0.68  fof(f14,axiom,(
% 0.39/0.68    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.39/0.68  fof(f37,plain,(
% 0.39/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.39/0.68    inference(cnf_transformation,[],[f4])).
% 0.39/0.68  fof(f4,axiom,(
% 0.39/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.39/0.68  fof(f24,plain,(
% 0.39/0.68    k1_xboole_0 != sK1),
% 0.39/0.68    inference(cnf_transformation,[],[f18])).
% 0.39/0.68  fof(f584,plain,(
% 0.39/0.68    sK2 = k2_xboole_0(sK1,sK2)),
% 0.39/0.68    inference(backward_demodulation,[],[f544,f546])).
% 0.39/0.68  fof(f544,plain,(
% 0.39/0.68    sK2 = k2_xboole_0(k2_xboole_0(sK1,sK2),sK2)),
% 0.39/0.68    inference(unit_resulting_resolution,[],[f503,f36])).
% 0.39/0.68  fof(f36,plain,(
% 0.39/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.39/0.68    inference(cnf_transformation,[],[f20])).
% 0.39/0.68  fof(f20,plain,(
% 0.39/0.68    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.39/0.68    inference(ennf_transformation,[],[f3])).
% 0.39/0.68  fof(f3,axiom,(
% 0.39/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.39/0.68  fof(f503,plain,(
% 0.39/0.68    r1_tarski(k2_xboole_0(sK1,sK2),sK2)),
% 0.39/0.68    inference(forward_demodulation,[],[f494,f53])).
% 0.39/0.68  fof(f494,plain,(
% 0.39/0.68    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK2)),
% 0.39/0.68    inference(backward_demodulation,[],[f165,f482])).
% 0.39/0.68  fof(f482,plain,(
% 0.39/0.68    sK0 = sK3(sK2)),
% 0.39/0.68    inference(unit_resulting_resolution,[],[f167,f183])).
% 0.39/0.68  fof(f183,plain,(
% 0.39/0.68    ( ! [X3] : (~r2_hidden(X3,k2_xboole_0(sK1,sK2)) | sK0 = X3) )),
% 0.39/0.68    inference(duplicate_literal_removal,[],[f179])).
% 0.39/0.68  fof(f179,plain,(
% 0.39/0.68    ( ! [X3] : (~r2_hidden(X3,k2_xboole_0(sK1,sK2)) | sK0 = X3 | sK0 = X3 | sK0 = X3) )),
% 0.39/0.68    inference(superposition,[],[f78,f53])).
% 0.39/0.68  fof(f78,plain,(
% 0.39/0.68    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.39/0.68    inference(equality_resolution,[],[f62])).
% 0.39/0.68  fof(f62,plain,(
% 0.39/0.68    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.39/0.68    inference(definition_unfolding,[],[f45,f50])).
% 0.39/0.68  fof(f45,plain,(
% 0.39/0.68    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.39/0.68    inference(cnf_transformation,[],[f21])).
% 0.39/0.68  fof(f21,plain,(
% 0.39/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.39/0.68    inference(ennf_transformation,[],[f5])).
% 0.39/0.68  fof(f5,axiom,(
% 0.39/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.39/0.68  fof(f167,plain,(
% 0.39/0.68    ( ! [X0] : (r2_hidden(sK3(sK2),k2_xboole_0(X0,sK2))) )),
% 0.39/0.68    inference(unit_resulting_resolution,[],[f125,f69])).
% 0.39/0.68  fof(f69,plain,(
% 0.39/0.68    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.39/0.68    inference(equality_resolution,[],[f35])).
% 0.39/0.68  fof(f35,plain,(
% 0.39/0.68    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.39/0.68    inference(cnf_transformation,[],[f1])).
% 0.39/0.68  fof(f1,axiom,(
% 0.39/0.68    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.39/0.68  fof(f125,plain,(
% 0.39/0.68    r2_hidden(sK3(sK2),sK2)),
% 0.39/0.68    inference(unit_resulting_resolution,[],[f25,f29])).
% 0.39/0.68  fof(f29,plain,(
% 0.39/0.68    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.39/0.68    inference(cnf_transformation,[],[f19])).
% 0.39/0.68  fof(f19,plain,(
% 0.39/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.39/0.68    inference(ennf_transformation,[],[f2])).
% 0.39/0.68  fof(f2,axiom,(
% 0.39/0.68    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.39/0.68  fof(f25,plain,(
% 0.39/0.68    k1_xboole_0 != sK2),
% 0.39/0.68    inference(cnf_transformation,[],[f18])).
% 0.39/0.68  fof(f165,plain,(
% 0.39/0.68    r1_tarski(k2_enumset1(sK3(sK2),sK3(sK2),sK3(sK2),sK3(sK2)),sK2)),
% 0.39/0.68    inference(unit_resulting_resolution,[],[f125,f58])).
% 0.39/0.68  fof(f58,plain,(
% 0.39/0.68    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.39/0.68    inference(definition_unfolding,[],[f38,f52])).
% 0.39/0.68  fof(f38,plain,(
% 0.39/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.39/0.68    inference(cnf_transformation,[],[f13])).
% 0.39/0.68  fof(f13,axiom,(
% 0.39/0.68    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.39/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.39/0.68  fof(f23,plain,(
% 0.39/0.68    sK1 != sK2),
% 0.39/0.68    inference(cnf_transformation,[],[f18])).
% 0.39/0.68  % SZS output end Proof for theBenchmark
% 0.39/0.68  % (21642)------------------------------
% 0.39/0.68  % (21642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.68  % (21642)Termination reason: Refutation
% 0.39/0.68  
% 0.39/0.68  % (21642)Memory used [KB]: 6652
% 0.39/0.68  % (21642)Time elapsed: 0.106 s
% 0.39/0.68  % (21642)------------------------------
% 0.39/0.68  % (21642)------------------------------
% 0.39/0.68  % (21416)Success in time 0.316 s
%------------------------------------------------------------------------------
