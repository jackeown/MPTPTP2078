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
% DateTime   : Thu Dec  3 12:43:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 129 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 331 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f763,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f321,f334,f762])).

fof(f762,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f752,f407])).

fof(f407,plain,(
    ! [X0] : r1_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f172,f172,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | r1_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f172,plain,(
    ! [X0] : ~ r2_hidden(sK3,k3_xboole_0(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f131,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f131,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f63,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f55,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f29,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f28,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f752,plain,
    ( ~ r1_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(sK0,sK1))
    | spl6_5 ),
    inference(resolution,[],[f317,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f317,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl6_5
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f334,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f329,f320])).

fof(f320,plain,
    ( ! [X4] : ~ r2_hidden(X4,k3_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl6_6
  <=> ! [X4] : ~ r2_hidden(X4,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f329,plain,(
    r2_hidden(sK5(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f293,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f293,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f291,f34])).

fof(f291,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f286,f63])).

fof(f286,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f77,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f77,plain,(
    r2_hidden(sK5(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f73,f45])).

fof(f73,plain,(
    r2_hidden(sK5(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f42])).

fof(f30,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f321,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f309,f319,f315])).

fof(f309,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k3_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3)) ) ),
    inference(superposition,[],[f41,f97])).

fof(f97,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f47,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3)) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15411)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15418)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (15431)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (15423)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15417)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (15426)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (15412)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (15415)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (15419)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (15428)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (15413)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15431)Refutation not found, incomplete strategy% (15431)------------------------------
% 0.21/0.53  % (15431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15431)Memory used [KB]: 10746
% 0.21/0.53  % (15431)Time elapsed: 0.057 s
% 0.21/0.53  % (15431)------------------------------
% 0.21/0.53  % (15431)------------------------------
% 0.21/0.54  % (15421)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (15414)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (15410)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (15435)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (15436)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (15437)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (15438)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (15429)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (15433)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (15430)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (15427)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (15425)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (15420)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (15422)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (15409)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (15432)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (15418)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f763,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f321,f334,f762])).
% 0.21/0.57  fof(f762,plain,(
% 0.21/0.57    spl6_5),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f761])).
% 0.21/0.57  fof(f761,plain,(
% 0.21/0.57    $false | spl6_5),
% 0.21/0.57    inference(subsumption_resolution,[],[f752,f407])).
% 0.21/0.57  fof(f407,plain,(
% 0.21/0.57    ( ! [X0] : (r1_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(X0,sK1))) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f172,f172,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | r1_xboole_0(k2_tarski(X0,X2),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.21/0.57  fof(f172,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK3,k3_xboole_0(X0,sK1))) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f131,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ~r2_hidden(sK3,sK1)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f28,f63,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f55,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK1))) )),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f29,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    inference(rectify,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    r1_xboole_0(sK2,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.57    inference(negated_conjecture,[],[f16])).
% 0.21/0.57  fof(f16,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    r2_hidden(sK3,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f752,plain,(
% 0.21/0.57    ~r1_xboole_0(k2_tarski(sK3,sK3),k3_xboole_0(sK0,sK1)) | spl6_5),
% 0.21/0.57    inference(resolution,[],[f317,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.57  fof(f317,plain,(
% 0.21/0.57    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3)) | spl6_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f315])).
% 0.21/0.57  fof(f315,plain,(
% 0.21/0.57    spl6_5 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.57  fof(f334,plain,(
% 0.21/0.57    ~spl6_6),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f333])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    $false | ~spl6_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f329,f320])).
% 0.21/0.57  fof(f320,plain,(
% 0.21/0.57    ( ! [X4] : (~r2_hidden(X4,k3_xboole_0(sK0,sK1))) ) | ~spl6_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f319])).
% 0.21/0.57  fof(f319,plain,(
% 0.21/0.57    spl6_6 <=> ! [X4] : ~r2_hidden(X4,k3_xboole_0(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.57  fof(f329,plain,(
% 0.21/0.57    r2_hidden(sK5(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.57    inference(resolution,[],[f293,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f291,f34])).
% 0.21/0.57  fof(f291,plain,(
% 0.21/0.57    ~r1_xboole_0(sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f286,f63])).
% 0.21/0.57  fof(f286,plain,(
% 0.21/0.57    r2_hidden(sK5(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK1,sK0)),
% 0.21/0.57    inference(superposition,[],[f77,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    r2_hidden(sK5(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))),
% 0.21/0.57    inference(forward_demodulation,[],[f73,f45])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    r2_hidden(sK5(k2_xboole_0(sK0,sK2),sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f30,f42])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f321,plain,(
% 0.21/0.57    ~spl6_5 | spl6_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f309,f319,f315])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    ( ! [X4] : (~r2_hidden(X4,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3))) )),
% 0.21/0.57    inference(superposition,[],[f41,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3))),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f47,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3))),
% 0.21/0.57    inference(definition_unfolding,[],[f27,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (15418)------------------------------
% 0.21/0.57  % (15418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15418)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (15418)Memory used [KB]: 11129
% 0.21/0.57  % (15418)Time elapsed: 0.138 s
% 0.21/0.57  % (15418)------------------------------
% 0.21/0.57  % (15418)------------------------------
% 0.21/0.58  % (15405)Success in time 0.207 s
%------------------------------------------------------------------------------
