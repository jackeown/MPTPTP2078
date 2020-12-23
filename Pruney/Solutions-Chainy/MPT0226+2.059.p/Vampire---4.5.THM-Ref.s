%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   66 (  94 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 238 expanded)
%              Number of equality atoms :   66 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f267,f292,f307,f313,f384])).

% (5667)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f384,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f47,f291])).

fof(f291,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl4_7
  <=> ! [X2] : ~ r2_hidden(X2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

% (5665)Refutation not found, incomplete strategy% (5665)------------------------------
% (5665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5671)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (5657)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (5670)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (5674)Refutation not found, incomplete strategy% (5674)------------------------------
% (5674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5674)Termination reason: Refutation not found, incomplete strategy

% (5674)Memory used [KB]: 6140
% (5674)Time elapsed: 0.122 s
% (5674)------------------------------
% (5674)------------------------------
fof(f47,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f313,plain,
    ( spl4_1
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f310,f52])).

fof(f52,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f310,plain,
    ( sK0 = sK1
    | ~ spl4_8 ),
    inference(resolution,[],[f306,f48])).

fof(f48,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f306,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f307,plain,
    ( spl4_8
    | spl4_4 ),
    inference(avatar_split_clause,[],[f302,f274,f304])).

fof(f274,plain,
    ( spl4_4
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f302,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | spl4_4 ),
    inference(resolution,[],[f276,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f276,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f274])).

fof(f292,plain,
    ( ~ spl4_4
    | spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f272,f264,f290,f274])).

fof(f264,plain,
    ( spl4_3
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f272,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_tarski(sK0))
        | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    | ~ spl4_3 ),
    inference(superposition,[],[f43,f266])).

fof(f266,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f264])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f267,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f262,f55,f264])).

fof(f55,plain,
    ( spl4_2
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f262,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f251,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f251,plain,
    ( k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f107,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f107,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f102,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f102,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(backward_demodulation,[],[f62,f94])).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f85,f37])).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f62,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f62,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f32,f38])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:38:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (5653)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (5650)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (5652)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (5649)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (5649)Refutation not found, incomplete strategy% (5649)------------------------------
% 0.21/0.51  % (5649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5649)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5649)Memory used [KB]: 1663
% 0.21/0.51  % (5649)Time elapsed: 0.106 s
% 0.21/0.51  % (5649)------------------------------
% 0.21/0.51  % (5649)------------------------------
% 0.21/0.51  % (5677)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (5677)Refutation not found, incomplete strategy% (5677)------------------------------
% 0.21/0.51  % (5677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5656)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (5662)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (5669)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (5674)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (5661)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (5648)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (5655)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (5668)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (5664)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (5669)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (5677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5677)Memory used [KB]: 1663
% 0.21/0.52  % (5677)Time elapsed: 0.117 s
% 0.21/0.52  % (5677)------------------------------
% 0.21/0.52  % (5677)------------------------------
% 0.21/0.52  % (5663)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (5664)Refutation not found, incomplete strategy% (5664)------------------------------
% 0.21/0.52  % (5664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5673)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (5662)Refutation not found, incomplete strategy% (5662)------------------------------
% 0.21/0.53  % (5662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5662)Memory used [KB]: 1663
% 0.21/0.53  % (5662)Time elapsed: 0.115 s
% 0.21/0.53  % (5662)------------------------------
% 0.21/0.53  % (5662)------------------------------
% 0.21/0.53  % (5651)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (5654)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (5658)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (5666)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (5664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5664)Memory used [KB]: 10618
% 0.21/0.53  % (5664)Time elapsed: 0.115 s
% 0.21/0.53  % (5664)------------------------------
% 0.21/0.53  % (5664)------------------------------
% 0.21/0.53  % (5666)Refutation not found, incomplete strategy% (5666)------------------------------
% 0.21/0.53  % (5666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5672)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (5666)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5666)Memory used [KB]: 1663
% 0.21/0.53  % (5666)Time elapsed: 0.126 s
% 0.21/0.53  % (5666)------------------------------
% 0.21/0.53  % (5666)------------------------------
% 0.21/0.53  % (5672)Refutation not found, incomplete strategy% (5672)------------------------------
% 0.21/0.53  % (5672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5672)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5672)Memory used [KB]: 10618
% 0.21/0.53  % (5672)Time elapsed: 0.128 s
% 0.21/0.53  % (5672)------------------------------
% 0.21/0.53  % (5672)------------------------------
% 0.21/0.54  % (5676)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (5665)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f53,f58,f267,f292,f307,f313,f384])).
% 0.21/0.54  % (5667)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  fof(f384,plain,(
% 0.21/0.54    ~spl4_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    $false | ~spl4_7),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f47,f291])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK0))) ) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f290])).
% 0.21/0.54  fof(f290,plain,(
% 0.21/0.54    spl4_7 <=> ! [X2] : ~r2_hidden(X2,k1_tarski(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.38/0.54  % (5665)Refutation not found, incomplete strategy% (5665)------------------------------
% 1.38/0.54  % (5665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (5671)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.54  % (5657)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.54  % (5670)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.54  % (5674)Refutation not found, incomplete strategy% (5674)------------------------------
% 1.38/0.54  % (5674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (5674)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (5674)Memory used [KB]: 6140
% 1.38/0.54  % (5674)Time elapsed: 0.122 s
% 1.38/0.54  % (5674)------------------------------
% 1.38/0.54  % (5674)------------------------------
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.38/0.54    inference(equality_resolution,[],[f46])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.38/0.54    inference(equality_resolution,[],[f34])).
% 1.38/0.54  fof(f34,plain,(
% 1.38/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.38/0.54    inference(cnf_transformation,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.38/0.54    inference(rectify,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.38/0.54    inference(nnf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.38/0.54  fof(f313,plain,(
% 1.38/0.54    spl4_1 | ~spl4_8),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f312])).
% 1.38/0.54  fof(f312,plain,(
% 1.38/0.54    $false | (spl4_1 | ~spl4_8)),
% 1.38/0.54    inference(subsumption_resolution,[],[f310,f52])).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    sK0 != sK1 | spl4_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f50])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    spl4_1 <=> sK0 = sK1),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.38/0.54  fof(f310,plain,(
% 1.38/0.54    sK0 = sK1 | ~spl4_8),
% 1.38/0.54    inference(resolution,[],[f306,f48])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.38/0.54    inference(equality_resolution,[],[f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.38/0.54    inference(cnf_transformation,[],[f27])).
% 1.38/0.54  fof(f306,plain,(
% 1.38/0.54    r2_hidden(sK0,k1_tarski(sK1)) | ~spl4_8),
% 1.38/0.54    inference(avatar_component_clause,[],[f304])).
% 1.38/0.54  fof(f304,plain,(
% 1.38/0.54    spl4_8 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.38/0.54  fof(f307,plain,(
% 1.38/0.54    spl4_8 | spl4_4),
% 1.38/0.54    inference(avatar_split_clause,[],[f302,f274,f304])).
% 1.38/0.54  fof(f274,plain,(
% 1.38/0.54    spl4_4 <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.38/0.54  fof(f302,plain,(
% 1.38/0.54    r2_hidden(sK0,k1_tarski(sK1)) | spl4_4),
% 1.38/0.54    inference(resolution,[],[f276,f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.38/0.54    inference(ennf_transformation,[],[f15])).
% 1.38/0.54  fof(f15,axiom,(
% 1.38/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.38/0.54  fof(f276,plain,(
% 1.38/0.54    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl4_4),
% 1.38/0.54    inference(avatar_component_clause,[],[f274])).
% 1.38/0.54  fof(f292,plain,(
% 1.38/0.54    ~spl4_4 | spl4_7 | ~spl4_3),
% 1.38/0.54    inference(avatar_split_clause,[],[f272,f264,f290,f274])).
% 1.38/0.54  fof(f264,plain,(
% 1.38/0.54    spl4_3 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.38/0.54  fof(f272,plain,(
% 1.38/0.54    ( ! [X2] : (~r2_hidden(X2,k1_tarski(sK0)) | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ) | ~spl4_3),
% 1.38/0.54    inference(superposition,[],[f43,f266])).
% 1.38/0.54  fof(f266,plain,(
% 1.38/0.54    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl4_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f264])).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f21,plain,(
% 1.38/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(ennf_transformation,[],[f18])).
% 1.38/0.54  fof(f18,plain,(
% 1.38/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.54    inference(rectify,[],[f2])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.38/0.54  fof(f267,plain,(
% 1.38/0.54    spl4_3 | ~spl4_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f262,f55,f264])).
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    spl4_2 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.38/0.54  fof(f262,plain,(
% 1.38/0.54    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl4_2),
% 1.38/0.54    inference(forward_demodulation,[],[f251,f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.38/0.54  fof(f251,plain,(
% 1.38/0.54    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) | ~spl4_2),
% 1.38/0.54    inference(superposition,[],[f107,f57])).
% 1.38/0.54  fof(f57,plain,(
% 1.38/0.54    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl4_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f55])).
% 1.38/0.54  fof(f107,plain,(
% 1.38/0.54    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.38/0.54    inference(superposition,[],[f102,f39])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.54  fof(f102,plain,(
% 1.38/0.54    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.38/0.54    inference(backward_demodulation,[],[f62,f94])).
% 1.38/0.54  fof(f94,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.38/0.54    inference(forward_demodulation,[],[f85,f37])).
% 1.38/0.54  fof(f85,plain,(
% 1.38/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.38/0.54    inference(superposition,[],[f62,f38])).
% 1.38/0.54  fof(f38,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.38/0.54    inference(superposition,[],[f32,f38])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.38/0.54  fof(f58,plain,(
% 1.38/0.54    spl4_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f30,f55])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.38/0.54    inference(cnf_transformation,[],[f23])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.38/0.54    inference(ennf_transformation,[],[f17])).
% 1.38/0.54  fof(f17,negated_conjecture,(
% 1.38/0.54    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.38/0.54    inference(negated_conjecture,[],[f16])).
% 1.38/0.54  fof(f16,conjecture,(
% 1.38/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.38/0.54  fof(f53,plain,(
% 1.38/0.54    ~spl4_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f31,f50])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    sK0 != sK1),
% 1.38/0.54    inference(cnf_transformation,[],[f23])).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (5669)------------------------------
% 1.38/0.54  % (5669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (5669)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (5669)Memory used [KB]: 6396
% 1.38/0.54  % (5669)Time elapsed: 0.135 s
% 1.38/0.54  % (5669)------------------------------
% 1.38/0.54  % (5669)------------------------------
% 1.38/0.54  % (5665)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (5665)Memory used [KB]: 1791
% 1.38/0.54  % (5665)Time elapsed: 0.137 s
% 1.38/0.54  % (5665)------------------------------
% 1.38/0.54  % (5665)------------------------------
% 1.38/0.54  % (5647)Success in time 0.184 s
%------------------------------------------------------------------------------
