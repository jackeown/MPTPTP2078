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
% DateTime   : Thu Dec  3 12:37:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 150 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 ( 340 expanded)
%              Number of equality atoms :   64 ( 141 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f65,f71,f350,f359])).

fof(f359,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f352])).

fof(f352,plain,
    ( $false
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f286,f46,f341,f331])).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f102,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f29,f34])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f341,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl5_10
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f46,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f21,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f286,plain,(
    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f281,f227])).

fof(f227,plain,(
    ! [X5] : r2_hidden(X5,k2_enumset1(X5,X5,X5,X5)) ),
    inference(resolution,[],[f216,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f216,plain,(
    ! [X5] : r1_tarski(X5,X5) ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X5,X5) ) ),
    inference(superposition,[],[f35,f203])).

fof(f203,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f86,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f51,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f52,f24])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f281,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK1,X6)
      | r1_tarski(sK0,X6) ) ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK0,X6)
      | ~ r2_hidden(sK1,X6) ) ),
    inference(superposition,[],[f35,f262])).

fof(f262,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(sK0,X1)
      | ~ r2_hidden(sK1,X1) ) ),
    inference(resolution,[],[f254,f51])).

fof(f254,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k4_xboole_0(sK0,X0))
      | k1_xboole_0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f202,f98])).

fof(f98,plain,(
    ! [X1] :
      ( r1_xboole_0(X1,sK0)
      | r2_hidden(sK1,X1) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X1] :
      ( r2_hidden(sK1,X1)
      | r1_xboole_0(X1,sK0)
      | r1_xboole_0(X1,sK0) ) ),
    inference(superposition,[],[f27,f74])).

fof(f74,plain,(
    ! [X0] :
      ( sK1 = sK3(X0,sK0)
      | r1_xboole_0(X0,sK0) ) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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

% (3661)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f202,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X1,X2),X1)
      | k1_xboole_0 = k4_xboole_0(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_xboole_0(k4_xboole_0(X1,X2),X1) ) ),
    inference(resolution,[],[f86,f175])).

fof(f175,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(X2),X3)
      | k1_xboole_0 = X2
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f81,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f350,plain,
    ( ~ spl5_3
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl5_3
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f342,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f342,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f340])).

fof(f70,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f71,plain,
    ( spl5_2
    | spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f66,f55,f68,f59])).

fof(f59,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f55,plain,
    ( spl5_1
  <=> sK1 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f66,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(superposition,[],[f24,f57])).

fof(f57,plain,
    ( sK1 = sK2(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f65,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f22,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f53,f59,f55])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | sK1 = sK2(sK0) ),
    inference(resolution,[],[f24,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (3659)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.49  % (3674)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.50  % (3668)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (3666)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (3684)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (3668)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (3655)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (3664)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (3660)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (3676)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (3684)Refutation not found, incomplete strategy% (3684)------------------------------
% 0.20/0.51  % (3684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3656)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (3684)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3684)Memory used [KB]: 1663
% 0.20/0.51  % (3684)Time elapsed: 0.002 s
% 0.20/0.51  % (3684)------------------------------
% 0.20/0.51  % (3684)------------------------------
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f360,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f62,f65,f71,f350,f359])).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    ~spl5_10),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f352])).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    $false | ~spl5_10),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f286,f46,f341,f331])).
% 0.20/0.52  fof(f331,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f324])).
% 0.20/0.52  fof(f324,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(superposition,[],[f102,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(superposition,[],[f29,f34])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.20/0.52  fof(f341,plain,(
% 0.20/0.52    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl5_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f340])).
% 0.20/0.52  fof(f340,plain,(
% 0.20/0.52    spl5_10 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.20/0.52    inference(definition_unfolding,[],[f21,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f23,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f25,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    sK0 != k1_tarski(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.52    inference(resolution,[],[f281,f227])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    ( ! [X5] : (r2_hidden(X5,k2_enumset1(X5,X5,X5,X5))) )),
% 0.20/0.52    inference(resolution,[],[f216,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f33,f45])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    ( ! [X5] : (r1_tarski(X5,X5)) )),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f209])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X5,X5)) )),
% 0.20/0.52    inference(superposition,[],[f35,f203])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f192])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f86,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK2(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.52    inference(resolution,[],[f51,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.52    inference(resolution,[],[f52,f24])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ( ! [X6] : (~r2_hidden(sK1,X6) | r1_tarski(sK0,X6)) )),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f272])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,X6) | ~r2_hidden(sK1,X6)) )),
% 0.20/0.52    inference(superposition,[],[f35,f262])).
% 0.20/0.52  fof(f262,plain,(
% 0.20/0.52    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK0,X1) | ~r2_hidden(sK1,X1)) )),
% 0.20/0.52    inference(resolution,[],[f254,f51])).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK1,k4_xboole_0(sK0,X0)) | k1_xboole_0 = k4_xboole_0(sK0,X0)) )),
% 0.20/0.52    inference(resolution,[],[f202,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X1] : (r1_xboole_0(X1,sK0) | r2_hidden(sK1,X1)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK1,X1) | r1_xboole_0(X1,sK0) | r1_xboole_0(X1,sK0)) )),
% 0.20/0.52    inference(superposition,[],[f27,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 = sK3(X0,sK0) | r1_xboole_0(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f28,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f2])).
% 0.20/0.52  % (3661)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~r1_xboole_0(k4_xboole_0(X1,X2),X1) | k1_xboole_0 = k4_xboole_0(X1,X2)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f193])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 0.20/0.52    inference(resolution,[],[f86,f175])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r2_hidden(sK2(X2),X3) | k1_xboole_0 = X2 | ~r1_xboole_0(X2,X3)) )),
% 0.20/0.52    inference(superposition,[],[f81,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    ~spl5_3 | spl5_10),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f348])).
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    $false | (~spl5_3 | spl5_10)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f70,f342,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f32,f45])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f342,plain,(
% 0.20/0.52    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl5_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f340])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    r2_hidden(sK1,sK0) | ~spl5_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl5_3 <=> r2_hidden(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    spl5_2 | spl5_3 | ~spl5_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f66,f55,f68,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl5_2 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl5_1 <=> sK1 = sK2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0 | ~spl5_1),
% 0.20/0.52    inference(superposition,[],[f24,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    sK1 = sK2(sK0) | ~spl5_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f55])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ~spl5_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    $false | ~spl5_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f22,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl5_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f59])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    k1_xboole_0 != sK0),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl5_1 | spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f53,f59,f55])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | sK1 = sK2(sK0)),
% 0.20/0.52    inference(resolution,[],[f24,f20])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (3668)------------------------------
% 0.20/0.52  % (3668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3668)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (3668)Memory used [KB]: 6396
% 0.20/0.52  % (3668)Time elapsed: 0.104 s
% 0.20/0.52  % (3668)------------------------------
% 0.20/0.52  % (3668)------------------------------
% 0.20/0.52  % (3654)Success in time 0.167 s
%------------------------------------------------------------------------------
