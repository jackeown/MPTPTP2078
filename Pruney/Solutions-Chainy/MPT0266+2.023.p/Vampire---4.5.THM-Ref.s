%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:30 EST 2020

% Result     : Theorem 2.51s
% Output     : Refutation 2.51s
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
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f85,f194])).

fof(f194,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f191,f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f191,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f86,f106])).

fof(f106,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k2_tarski(sK0,sK1))
        | r2_hidden(X6,sK2) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,
    ( ! [X6] :
        ( r2_hidden(X6,sK2)
        | ~ r2_hidden(X6,k2_tarski(sK0,sK1))
        | ~ r2_hidden(X6,k2_tarski(sK0,sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f42,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
        | ~ r2_hidden(X0,k2_tarski(sK0,sK1)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f84,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f64,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f85,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f80,f72,f82])).

fof(f72,plain,
    ( spl5_2
  <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f80,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f76,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f76,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl5_2 ),
    inference(superposition,[],[f56,f74])).

fof(f74,plain,
    ( k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f56,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f75,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f70,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:58:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (14081)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.45  % (14073)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.46  % (14065)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (14063)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (14086)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.50  % (14062)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (14076)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  % (14071)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (14061)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (14060)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (14084)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (14077)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.52  % (14064)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (14087)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (14058)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (14068)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.53  % (14059)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (14069)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (14072)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (14080)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.54  % (14074)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.54  % (14070)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.54  % (14079)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.54  % (14066)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.54  % (14082)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.55  % (14075)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.55  % (14085)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.55  % (14075)Refutation not found, incomplete strategy% (14075)------------------------------
% 1.49/0.55  % (14075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (14075)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (14075)Memory used [KB]: 10746
% 1.49/0.55  % (14075)Time elapsed: 0.156 s
% 1.49/0.55  % (14075)------------------------------
% 1.49/0.55  % (14075)------------------------------
% 1.60/0.55  % (14078)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.60/0.56  % (14083)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.60/0.56  % (14067)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.51/0.68  % (14184)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.51/0.69  % (14059)Refutation found. Thanks to Tanya!
% 2.51/0.69  % SZS status Theorem for theBenchmark
% 2.51/0.71  % SZS output start Proof for theBenchmark
% 2.51/0.72  fof(f195,plain,(
% 2.51/0.72    $false),
% 2.51/0.72    inference(avatar_sat_refutation,[],[f70,f75,f85,f194])).
% 2.51/0.72  fof(f194,plain,(
% 2.51/0.72    spl5_1 | ~spl5_3),
% 2.51/0.72    inference(avatar_contradiction_clause,[],[f193])).
% 2.51/0.72  fof(f193,plain,(
% 2.51/0.72    $false | (spl5_1 | ~spl5_3)),
% 2.51/0.72    inference(subsumption_resolution,[],[f191,f69])).
% 2.51/0.72  fof(f69,plain,(
% 2.51/0.72    ~r2_hidden(sK0,sK2) | spl5_1),
% 2.51/0.72    inference(avatar_component_clause,[],[f67])).
% 2.51/0.72  fof(f67,plain,(
% 2.51/0.72    spl5_1 <=> r2_hidden(sK0,sK2)),
% 2.51/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.51/0.72  fof(f191,plain,(
% 2.51/0.72    r2_hidden(sK0,sK2) | ~spl5_3),
% 2.51/0.72    inference(resolution,[],[f86,f106])).
% 2.51/0.72  fof(f106,plain,(
% 2.51/0.72    ( ! [X6] : (~r2_hidden(X6,k2_tarski(sK0,sK1)) | r2_hidden(X6,sK2)) ) | ~spl5_3),
% 2.51/0.72    inference(duplicate_literal_removal,[],[f103])).
% 2.51/0.72  fof(f103,plain,(
% 2.51/0.72    ( ! [X6] : (r2_hidden(X6,sK2) | ~r2_hidden(X6,k2_tarski(sK0,sK1)) | ~r2_hidden(X6,k2_tarski(sK0,sK1))) ) | ~spl5_3),
% 2.51/0.72    inference(resolution,[],[f42,f90])).
% 2.51/0.72  fof(f90,plain,(
% 2.51/0.72    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~r2_hidden(X0,k2_tarski(sK0,sK1))) ) | ~spl5_3),
% 2.51/0.72    inference(resolution,[],[f84,f44])).
% 2.51/0.72  fof(f44,plain,(
% 2.51/0.72    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.51/0.72    inference(cnf_transformation,[],[f29])).
% 2.51/0.72  fof(f29,plain,(
% 2.51/0.72    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.51/0.72    inference(ennf_transformation,[],[f23])).
% 2.51/0.72  fof(f23,plain,(
% 2.51/0.72    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.51/0.72    inference(rectify,[],[f5])).
% 2.51/0.72  fof(f5,axiom,(
% 2.51/0.72    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.51/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.51/0.72  fof(f84,plain,(
% 2.51/0.72    r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl5_3),
% 2.51/0.72    inference(avatar_component_clause,[],[f82])).
% 2.51/0.72  fof(f82,plain,(
% 2.51/0.72    spl5_3 <=> r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.51/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.51/0.72  fof(f42,plain,(
% 2.51/0.72    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.51/0.72    inference(cnf_transformation,[],[f28])).
% 2.51/0.72  fof(f28,plain,(
% 2.51/0.72    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.51/0.72    inference(ennf_transformation,[],[f4])).
% 2.51/0.72  fof(f4,axiom,(
% 2.51/0.72    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.51/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.51/0.72  fof(f86,plain,(
% 2.51/0.72    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.51/0.72    inference(superposition,[],[f64,f52])).
% 2.51/0.72  fof(f52,plain,(
% 2.51/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.51/0.72    inference(cnf_transformation,[],[f15])).
% 2.51/0.72  fof(f15,axiom,(
% 2.51/0.72    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.51/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.51/0.72  fof(f64,plain,(
% 2.51/0.72    ( ! [X4,X2,X1] : (r2_hidden(X4,k1_enumset1(X4,X1,X2))) )),
% 2.51/0.72    inference(equality_resolution,[],[f63])).
% 2.51/0.72  fof(f63,plain,(
% 2.51/0.72    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X4,X1,X2) != X3) )),
% 2.51/0.72    inference(equality_resolution,[],[f37])).
% 2.51/0.72  fof(f37,plain,(
% 2.51/0.72    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.51/0.72    inference(cnf_transformation,[],[f27])).
% 2.51/0.72  fof(f27,plain,(
% 2.51/0.72    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.51/0.72    inference(ennf_transformation,[],[f10])).
% 2.51/0.72  fof(f10,axiom,(
% 2.51/0.72    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.51/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.51/0.72  fof(f85,plain,(
% 2.51/0.72    spl5_3 | ~spl5_2),
% 2.51/0.72    inference(avatar_split_clause,[],[f80,f72,f82])).
% 2.51/0.72  fof(f72,plain,(
% 2.51/0.72    spl5_2 <=> k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.51/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.51/0.72  fof(f80,plain,(
% 2.51/0.72    r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl5_2),
% 2.51/0.72    inference(forward_demodulation,[],[f76,f53])).
% 2.51/0.72  fof(f53,plain,(
% 2.51/0.72    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.51/0.72    inference(cnf_transformation,[],[f1])).
% 2.51/0.72  fof(f1,axiom,(
% 2.51/0.72    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.51/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.51/0.72  fof(f76,plain,(
% 2.51/0.72    r1_xboole_0(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~spl5_2),
% 2.51/0.72    inference(superposition,[],[f56,f74])).
% 2.51/0.72  fof(f74,plain,(
% 2.51/0.72    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_2),
% 2.51/0.72    inference(avatar_component_clause,[],[f72])).
% 2.51/0.72  fof(f56,plain,(
% 2.51/0.72    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.51/0.72    inference(cnf_transformation,[],[f6])).
% 2.51/0.72  fof(f6,axiom,(
% 2.51/0.72    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.51/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.51/0.72  fof(f75,plain,(
% 2.51/0.72    spl5_2),
% 2.51/0.72    inference(avatar_split_clause,[],[f30,f72])).
% 2.51/0.72  fof(f30,plain,(
% 2.51/0.72    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.51/0.72    inference(cnf_transformation,[],[f26])).
% 2.51/0.72  fof(f26,plain,(
% 2.51/0.72    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 2.51/0.72    inference(ennf_transformation,[],[f22])).
% 2.51/0.72  fof(f22,negated_conjecture,(
% 2.51/0.72    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 2.51/0.72    inference(negated_conjecture,[],[f21])).
% 2.51/0.72  fof(f21,conjecture,(
% 2.51/0.72    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 2.51/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).
% 2.51/0.72  fof(f70,plain,(
% 2.51/0.72    ~spl5_1),
% 2.51/0.72    inference(avatar_split_clause,[],[f31,f67])).
% 2.51/0.72  fof(f31,plain,(
% 2.51/0.72    ~r2_hidden(sK0,sK2)),
% 2.51/0.72    inference(cnf_transformation,[],[f26])).
% 2.51/0.72  % SZS output end Proof for theBenchmark
% 2.51/0.72  % (14059)------------------------------
% 2.51/0.72  % (14059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.72  % (14059)Termination reason: Refutation
% 2.51/0.72  
% 2.51/0.72  % (14059)Memory used [KB]: 6396
% 2.51/0.72  % (14059)Time elapsed: 0.283 s
% 2.51/0.72  % (14059)------------------------------
% 2.51/0.72  % (14059)------------------------------
% 2.51/0.72  % (14057)Success in time 0.379 s
%------------------------------------------------------------------------------
