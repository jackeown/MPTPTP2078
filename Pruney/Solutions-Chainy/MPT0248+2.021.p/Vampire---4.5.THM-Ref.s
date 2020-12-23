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
% DateTime   : Thu Dec  3 12:37:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 145 expanded)
%              Number of leaves         :   19 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  224 ( 465 expanded)
%              Number of equality atoms :  106 ( 280 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f68,f69,f74,f80,f98,f122,f148,f167,f173,f175,f224,f253])).

fof(f253,plain,(
    spl3_21 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl3_21 ),
    inference(subsumption_resolution,[],[f250,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f250,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_21 ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_21 ),
    inference(superposition,[],[f223,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f223,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl3_21
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f224,plain,
    ( ~ spl3_21
    | ~ spl3_2
    | ~ spl3_3
    | spl3_14 ),
    inference(avatar_split_clause,[],[f219,f164,f61,f56,f221])).

fof(f56,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f61,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f164,plain,
    ( spl3_14
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f219,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_14 ),
    inference(forward_demodulation,[],[f218,f62])).

fof(f62,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f218,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_2
    | spl3_14 ),
    inference(forward_demodulation,[],[f166,f57])).

fof(f57,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f166,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f175,plain,
    ( spl3_2
    | spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f174,f95,f65,f56])).

fof(f65,plain,
    ( spl3_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f95,plain,
    ( spl3_8
  <=> r1_tarski(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f174,plain,
    ( k1_xboole_0 = sK2
    | spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f171,f67])).

fof(f67,plain,
    ( sK2 != k1_tarski(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f171,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f31,f97])).

fof(f97,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f173,plain,
    ( spl3_3
    | spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f172,f77,f52,f61])).

fof(f52,plain,
    ( spl3_1
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f170,f54])).

fof(f54,plain,
    ( sK1 != k1_tarski(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f170,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f31,f79])).

fof(f79,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f167,plain,
    ( ~ spl3_14
    | spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f162,f145,f119,f164])).

fof(f119,plain,
    ( spl3_10
  <=> r1_tarski(k1_tarski(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f145,plain,
    ( spl3_12
  <=> k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f162,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f153,f121])).

fof(f121,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f153,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl3_12 ),
    inference(superposition,[],[f29,f147])).

fof(f147,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f145])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f148,plain,
    ( spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f136,f71,f145])).

fof(f71,plain,
    ( spl3_5
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f136,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f40,f73])).

fof(f73,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f122,plain,
    ( ~ spl3_10
    | spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f117,f95,f65,f119])).

fof(f117,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK2)
    | spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f110,f67])).

fof(f110,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f38,f97])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f91,f71,f95])).

fof(f91,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f88,f73])).

fof(f88,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f80,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f75,f71,f77])).

fof(f75,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_5 ),
    inference(superposition,[],[f43,f73])).

fof(f74,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f71])).

fof(f25,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f69,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f26,f65,f52])).

fof(f26,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f27,f65,f61])).

fof(f27,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f28,f56,f52])).

fof(f28,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (31705)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (31697)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (31687)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (31689)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (31684)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (31688)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31682)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (31703)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (31704)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (31703)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f254,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f59,f68,f69,f74,f80,f98,f122,f148,f167,f173,f175,f224,f253])).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    spl3_21),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f252])).
% 0.21/0.54  fof(f252,plain,(
% 0.21/0.54    $false | spl3_21),
% 0.21/0.54    inference(subsumption_resolution,[],[f250,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl3_21),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f249])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl3_21),
% 0.21/0.54    inference(superposition,[],[f223,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | spl3_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f221])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    spl3_21 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ~spl3_21 | ~spl3_2 | ~spl3_3 | spl3_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f219,f164,f61,f56,f221])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl3_2 <=> k1_xboole_0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    spl3_3 <=> k1_xboole_0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    spl3_14 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_2 | ~spl3_3 | spl3_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f218,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | ~spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f61])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) | (~spl3_2 | spl3_14)),
% 0.21/0.54    inference(forward_demodulation,[],[f166,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | ~spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f56])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(sK1,sK2) | spl3_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f164])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    spl3_2 | spl3_4 | ~spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f174,f95,f65,f56])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl3_4 <=> sK2 = k1_tarski(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    spl3_8 <=> r1_tarski(sK2,k1_tarski(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | (spl3_4 | ~spl3_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f171,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    sK2 != k1_tarski(sK0) | spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | sK2 = k1_tarski(sK0) | ~spl3_8),
% 0.21/0.54    inference(resolution,[],[f31,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    r1_tarski(sK2,k1_tarski(sK0)) | ~spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f95])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    spl3_3 | spl3_1 | ~spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f172,f77,f52,f61])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl3_1 <=> sK1 = k1_tarski(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl3_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | (spl3_1 | ~spl3_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f170,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    sK1 != k1_tarski(sK0) | spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f52])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0) | ~spl3_6),
% 0.21/0.54    inference(resolution,[],[f31,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f77])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ~spl3_14 | spl3_10 | ~spl3_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f162,f145,f119,f164])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl3_10 <=> r1_tarski(k1_tarski(sK0),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    spl3_12 <=> k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(sK1,sK2) | (spl3_10 | ~spl3_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f153,f121])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ~r1_tarski(k1_tarski(sK0),sK2) | spl3_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    k1_xboole_0 != k4_xboole_0(sK1,sK2) | r1_tarski(k1_tarski(sK0),sK2) | ~spl3_12),
% 0.21/0.54    inference(superposition,[],[f29,f147])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(sK1,sK2) | ~spl3_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f145])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    spl3_12 | ~spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f136,f71,f145])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl3_5 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(sK1,sK2) | ~spl3_5),
% 0.21/0.54    inference(superposition,[],[f40,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f71])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ~spl3_10 | spl3_4 | ~spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f117,f95,f65,f119])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ~r1_tarski(k1_tarski(sK0),sK2) | (spl3_4 | ~spl3_8)),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f67])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    sK2 = k1_tarski(sK0) | ~r1_tarski(k1_tarski(sK0),sK2) | ~spl3_8),
% 0.21/0.54    inference(resolution,[],[f38,f97])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl3_8 | ~spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f91,f71,f95])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    r1_tarski(sK2,k1_tarski(sK0)) | ~spl3_5),
% 0.21/0.54    inference(superposition,[],[f88,f73])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,X2))) )),
% 0.21/0.54    inference(superposition,[],[f43,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl3_6 | ~spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f75,f71,f77])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_5),
% 0.21/0.54    inference(superposition,[],[f43,f73])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f25,f71])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f15])).
% 0.21/0.54  fof(f15,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f26,f65,f52])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ~spl3_3 | ~spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f65,f61])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f56,f52])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (31703)------------------------------
% 0.21/0.54  % (31703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31703)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (31703)Memory used [KB]: 6396
% 0.21/0.54  % (31703)Time elapsed: 0.130 s
% 0.21/0.54  % (31703)------------------------------
% 0.21/0.54  % (31703)------------------------------
% 0.21/0.54  % (31685)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (31686)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (31683)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (31708)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (31694)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (31699)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (31700)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (31701)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (31681)Success in time 0.187 s
%------------------------------------------------------------------------------
