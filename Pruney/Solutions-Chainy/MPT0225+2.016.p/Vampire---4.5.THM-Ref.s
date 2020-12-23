%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 143 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 281 expanded)
%              Number of equality atoms :   59 ( 175 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f187,f215])).

fof(f215,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f48,f52,f191,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f191,plain,
    ( r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f189,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f189,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( sK0 != sK0
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f54,f62])).

fof(f62,plain,
    ( sK0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f54,plain,
    ( sK0 != sK1
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) ),
    inference(inner_rewriting,[],[f44])).

fof(f44,plain,
    ( sK0 != sK1
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f22,f42,f42,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f52,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f48,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k1_enumset1(X0,X1,X4)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f187,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f102,f115,f24])).

fof(f115,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( sK0 != sK0
    | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | spl4_1 ),
    inference(backward_demodulation,[],[f54,f98])).

fof(f98,plain,
    ( sK0 = sK1
    | spl4_1 ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | spl4_1 ),
    inference(resolution,[],[f83,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,
    ( r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f73,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f58,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_1
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f102,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))
    | spl4_1 ),
    inference(backward_demodulation,[],[f73,f98])).

fof(f63,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f43,f60,f56])).

fof(f43,plain,
    ( sK0 = sK1
    | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f23,f42,f42,f42])).

fof(f23,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (16087)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.48  % (16079)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (16076)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (16099)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (16085)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (16094)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (16074)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (16072)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (16086)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (16086)Refutation not found, incomplete strategy% (16086)------------------------------
% 0.20/0.52  % (16086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16086)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16086)Memory used [KB]: 1663
% 0.20/0.52  % (16086)Time elapsed: 0.085 s
% 0.20/0.52  % (16086)------------------------------
% 0.20/0.52  % (16086)------------------------------
% 0.20/0.52  % (16078)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (16099)Refutation not found, incomplete strategy% (16099)------------------------------
% 0.20/0.52  % (16099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16099)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16099)Memory used [KB]: 6140
% 0.20/0.52  % (16099)Time elapsed: 0.132 s
% 0.20/0.52  % (16099)------------------------------
% 0.20/0.52  % (16099)------------------------------
% 0.20/0.52  % (16095)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (16073)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (16073)Refutation not found, incomplete strategy% (16073)------------------------------
% 0.20/0.53  % (16073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16073)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16073)Memory used [KB]: 1663
% 0.20/0.53  % (16073)Time elapsed: 0.128 s
% 0.20/0.53  % (16073)------------------------------
% 0.20/0.53  % (16073)------------------------------
% 0.20/0.53  % (16084)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (16097)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (16093)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (16077)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (16097)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (16075)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (16089)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (16098)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (16089)Refutation not found, incomplete strategy% (16089)------------------------------
% 0.20/0.53  % (16089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16089)Memory used [KB]: 1663
% 0.20/0.53  % (16089)Time elapsed: 0.140 s
% 0.20/0.53  % (16089)------------------------------
% 0.20/0.53  % (16089)------------------------------
% 0.20/0.53  % (16098)Refutation not found, incomplete strategy% (16098)------------------------------
% 0.20/0.53  % (16098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16098)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16098)Memory used [KB]: 6140
% 0.20/0.53  % (16098)Time elapsed: 0.138 s
% 0.20/0.53  % (16098)------------------------------
% 0.20/0.53  % (16098)------------------------------
% 0.20/0.53  % (16088)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (16081)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (16100)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (16092)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (16091)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (16080)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (16101)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (16101)Refutation not found, incomplete strategy% (16101)------------------------------
% 0.20/0.54  % (16101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16101)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16101)Memory used [KB]: 1663
% 0.20/0.54  % (16101)Time elapsed: 0.003 s
% 0.20/0.54  % (16101)------------------------------
% 0.20/0.54  % (16101)------------------------------
% 0.20/0.54  % (16090)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (16082)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (16090)Refutation not found, incomplete strategy% (16090)------------------------------
% 0.20/0.55  % (16090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16090)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (16090)Memory used [KB]: 1663
% 0.20/0.55  % (16090)Time elapsed: 0.151 s
% 0.20/0.55  % (16090)------------------------------
% 0.20/0.55  % (16090)------------------------------
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f216,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f63,f187,f215])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    ~spl4_2),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f204])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    $false | ~spl4_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f48,f52,f191,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.55  fof(f191,plain,(
% 0.20/0.55    r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | ~spl4_2),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f189,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | ~spl4_2),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f188])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    sK0 != sK0 | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | ~spl4_2),
% 0.20/0.55    inference(backward_demodulation,[],[f54,f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    sK0 = sK1 | ~spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    spl4_2 <=> sK0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    sK0 != sK1 | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0))),
% 0.20/0.55    inference(inner_rewriting,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    sK0 != sK1 | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.55    inference(definition_unfolding,[],[f22,f42,f42,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f28,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.55    inference(negated_conjecture,[],[f13])).
% 0.20/0.55  fof(f13,conjecture,(
% 0.20/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X4,X2,X1] : (r2_hidden(X4,k1_enumset1(X4,X1,X2))) )),
% 0.20/0.55    inference(equality_resolution,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X4,X1,X2) != X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X4))) )),
% 0.20/0.55    inference(equality_resolution,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X0,X1,X4) != X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    spl4_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    $false | spl4_1),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f102,f115,f24])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | spl4_1),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    sK0 != sK0 | k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | spl4_1),
% 0.20/0.55    inference(backward_demodulation,[],[f54,f98])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    sK0 = sK1 | spl4_1),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | spl4_1),
% 0.20/0.55    inference(resolution,[],[f83,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.20/0.55    inference(equality_resolution,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | spl4_1),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f73,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f27,f42])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | spl4_1),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f58,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | spl4_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    spl4_1 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)) | spl4_1),
% 0.20/0.55    inference(backward_demodulation,[],[f73,f98])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ~spl4_1 | spl4_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f43,f60,f56])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    sK0 = sK1 | k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.20/0.55    inference(definition_unfolding,[],[f23,f42,f42,f42])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f16])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (16097)------------------------------
% 0.20/0.55  % (16097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16097)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (16097)Memory used [KB]: 6268
% 0.20/0.55  % (16097)Time elapsed: 0.134 s
% 0.20/0.55  % (16097)------------------------------
% 0.20/0.55  % (16097)------------------------------
% 0.20/0.55  % (16071)Success in time 0.189 s
%------------------------------------------------------------------------------
