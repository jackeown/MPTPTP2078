%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:30 EST 2020

% Result     : Theorem 2.83s
% Output     : Refutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 113 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f84,f176])).

fof(f176,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f174,f68])).

fof(f68,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f174,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f85,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | r2_hidden(X0,sK2) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK1))
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,k2_tarski(sK0,sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
        | ~ r2_hidden(X0,k2_tarski(sK0,sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f83,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f83,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f85,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f63,f55])).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f84,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f79,f71,f81])).

fof(f71,plain,
    ( spl5_2
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f75,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f75,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl5_2 ),
    inference(superposition,[],[f53,f73])).

fof(f73,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f74,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f69,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (7795)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (7810)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (7826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (7799)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (7811)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (7817)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (7804)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (7820)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (7801)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (7809)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (7800)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (7805)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (7798)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (7796)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (7808)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (7806)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (7823)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (7822)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (7814)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (7821)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (7814)Refutation not found, incomplete strategy% (7814)------------------------------
% 0.21/0.54  % (7814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7814)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7814)Memory used [KB]: 10618
% 0.21/0.54  % (7814)Time elapsed: 0.139 s
% 0.21/0.54  % (7814)------------------------------
% 0.21/0.54  % (7814)------------------------------
% 0.21/0.55  % (7825)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (7812)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (7827)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (7813)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (7816)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (7815)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (7807)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (7818)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (7802)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (7828)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.67  % (7859)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.83/0.76  % (7796)Refutation found. Thanks to Tanya!
% 2.83/0.76  % SZS status Theorem for theBenchmark
% 2.83/0.76  % SZS output start Proof for theBenchmark
% 2.83/0.76  fof(f177,plain,(
% 2.83/0.76    $false),
% 2.83/0.76    inference(avatar_sat_refutation,[],[f69,f74,f84,f176])).
% 2.83/0.76  fof(f176,plain,(
% 2.83/0.76    spl5_1 | ~spl5_3),
% 2.83/0.76    inference(avatar_contradiction_clause,[],[f175])).
% 2.83/0.76  fof(f175,plain,(
% 2.83/0.76    $false | (spl5_1 | ~spl5_3)),
% 2.83/0.76    inference(subsumption_resolution,[],[f174,f68])).
% 2.83/0.76  fof(f68,plain,(
% 2.83/0.76    ~r2_hidden(sK0,sK2) | spl5_1),
% 2.83/0.76    inference(avatar_component_clause,[],[f66])).
% 2.83/0.76  fof(f66,plain,(
% 2.83/0.76    spl5_1 <=> r2_hidden(sK0,sK2)),
% 2.83/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.83/0.76  fof(f174,plain,(
% 2.83/0.76    r2_hidden(sK0,sK2) | ~spl5_3),
% 2.83/0.76    inference(resolution,[],[f85,f107])).
% 2.83/0.76  fof(f107,plain,(
% 2.83/0.76    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK1)) | r2_hidden(X0,sK2)) ) | ~spl5_3),
% 2.83/0.76    inference(duplicate_literal_removal,[],[f104])).
% 2.83/0.76  fof(f104,plain,(
% 2.83/0.76    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK1)) | r2_hidden(X0,sK2) | ~r2_hidden(X0,k2_tarski(sK0,sK1))) ) | ~spl5_3),
% 2.83/0.76    inference(resolution,[],[f89,f43])).
% 2.83/0.76  fof(f43,plain,(
% 2.83/0.76    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.83/0.76    inference(cnf_transformation,[],[f29])).
% 2.83/0.76  fof(f29,plain,(
% 2.83/0.76    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.83/0.76    inference(ennf_transformation,[],[f4])).
% 2.83/0.76  fof(f4,axiom,(
% 2.83/0.76    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.83/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.83/0.76  fof(f89,plain,(
% 2.83/0.76    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~r2_hidden(X0,k2_tarski(sK0,sK1))) ) | ~spl5_3),
% 2.83/0.76    inference(resolution,[],[f83,f45])).
% 2.83/0.76  fof(f45,plain,(
% 2.83/0.76    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.83/0.76    inference(cnf_transformation,[],[f30])).
% 2.83/0.76  fof(f30,plain,(
% 2.83/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.83/0.76    inference(ennf_transformation,[],[f24])).
% 2.83/0.76  fof(f24,plain,(
% 2.83/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.83/0.76    inference(rectify,[],[f5])).
% 2.83/0.76  fof(f5,axiom,(
% 2.83/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.83/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.83/0.76  fof(f83,plain,(
% 2.83/0.76    r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl5_3),
% 2.83/0.76    inference(avatar_component_clause,[],[f81])).
% 2.83/0.76  fof(f81,plain,(
% 2.83/0.76    spl5_3 <=> r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.83/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.83/0.76  fof(f85,plain,(
% 2.83/0.76    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.83/0.76    inference(superposition,[],[f63,f55])).
% 2.83/0.76  fof(f55,plain,(
% 2.83/0.76    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.83/0.76    inference(cnf_transformation,[],[f15])).
% 2.83/0.76  fof(f15,axiom,(
% 2.83/0.76    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.83/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.83/0.76  fof(f63,plain,(
% 2.83/0.76    ( ! [X4,X2,X1] : (r2_hidden(X4,k1_enumset1(X4,X1,X2))) )),
% 2.83/0.76    inference(equality_resolution,[],[f62])).
% 2.83/0.76  fof(f62,plain,(
% 2.83/0.76    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X4,X1,X2) != X3) )),
% 2.83/0.76    inference(equality_resolution,[],[f38])).
% 2.83/0.76  fof(f38,plain,(
% 2.83/0.76    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.83/0.76    inference(cnf_transformation,[],[f28])).
% 2.83/0.76  fof(f28,plain,(
% 2.83/0.76    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.83/0.76    inference(ennf_transformation,[],[f10])).
% 2.83/0.76  fof(f10,axiom,(
% 2.83/0.76    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.83/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.83/0.76  fof(f84,plain,(
% 2.83/0.76    spl5_3 | ~spl5_2),
% 2.83/0.76    inference(avatar_split_clause,[],[f79,f71,f81])).
% 2.83/0.76  fof(f71,plain,(
% 2.83/0.76    spl5_2 <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.83/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.83/0.76  fof(f79,plain,(
% 2.83/0.76    r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl5_2),
% 2.83/0.76    inference(forward_demodulation,[],[f75,f50])).
% 2.83/0.76  fof(f50,plain,(
% 2.83/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.83/0.76    inference(cnf_transformation,[],[f1])).
% 2.83/0.76  fof(f1,axiom,(
% 2.83/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.83/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.83/0.76  fof(f75,plain,(
% 2.83/0.76    r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~spl5_2),
% 2.83/0.76    inference(superposition,[],[f53,f73])).
% 2.83/0.76  fof(f73,plain,(
% 2.83/0.76    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_2),
% 2.83/0.76    inference(avatar_component_clause,[],[f71])).
% 2.83/0.76  fof(f53,plain,(
% 2.83/0.76    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.83/0.76    inference(cnf_transformation,[],[f6])).
% 2.83/0.76  fof(f6,axiom,(
% 2.83/0.76    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.83/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.83/0.76  fof(f74,plain,(
% 2.83/0.76    spl5_2),
% 2.83/0.76    inference(avatar_split_clause,[],[f31,f71])).
% 2.83/0.76  fof(f31,plain,(
% 2.83/0.76    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.83/0.76    inference(cnf_transformation,[],[f27])).
% 2.83/0.76  fof(f27,plain,(
% 2.83/0.76    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 2.83/0.76    inference(ennf_transformation,[],[f23])).
% 2.83/0.76  fof(f23,negated_conjecture,(
% 2.83/0.76    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 2.83/0.76    inference(negated_conjecture,[],[f22])).
% 2.83/0.76  fof(f22,conjecture,(
% 2.83/0.76    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 2.83/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).
% 2.83/0.76  fof(f69,plain,(
% 2.83/0.76    ~spl5_1),
% 2.83/0.76    inference(avatar_split_clause,[],[f32,f66])).
% 2.83/0.76  fof(f32,plain,(
% 2.83/0.76    ~r2_hidden(sK0,sK2)),
% 2.83/0.76    inference(cnf_transformation,[],[f27])).
% 2.83/0.76  % SZS output end Proof for theBenchmark
% 2.83/0.76  % (7796)------------------------------
% 2.83/0.76  % (7796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.76  % (7796)Termination reason: Refutation
% 2.83/0.76  
% 2.83/0.76  % (7796)Memory used [KB]: 6396
% 2.83/0.76  % (7796)Time elapsed: 0.330 s
% 2.83/0.76  % (7796)------------------------------
% 2.83/0.76  % (7796)------------------------------
% 2.83/0.76  % (7791)Success in time 0.395 s
%------------------------------------------------------------------------------
