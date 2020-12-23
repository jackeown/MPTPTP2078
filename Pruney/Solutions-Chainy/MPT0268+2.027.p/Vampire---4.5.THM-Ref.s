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
% DateTime   : Thu Dec  3 12:40:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 122 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  215 ( 668 expanded)
%              Number of equality atoms :   43 ( 120 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f53,f150,f173,f197,f232])).

fof(f232,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f230,f50])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f230,plain,
    ( r2_hidden(sK1,sK0)
    | spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f229,f149])).

fof(f149,plain,
    ( sK1 = sK2(sK0,k1_tarski(sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_4
  <=> sK1 = sK2(sK0,k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f229,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(equality_resolution,[],[f201])).

fof(f201,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0)
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0) )
    | spl3_1 ),
    inference(superposition,[],[f47,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f47,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f197,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f188,f51])).

fof(f51,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f188,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_1 ),
    inference(superposition,[],[f40,f46])).

fof(f46,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f40,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f173,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f172,f144,f45])).

fof(f144,plain,
    ( spl3_3
  <=> ! [X0] : ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f172,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f159,f145])).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f159,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f145,f37])).

fof(f150,plain,
    ( spl3_3
    | spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f135,f45,f147,f144])).

fof(f135,plain,
    ( ! [X0] :
        ( sK1 = sK2(sK0,k1_tarski(sK1),sK0)
        | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),X0) )
    | spl3_1 ),
    inference(resolution,[],[f95,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k4_xboole_0(X0,k1_tarski(sK1)))
    | spl3_1 ),
    inference(resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f91,f85])).

fof(f85,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0)
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0) )
    | spl3_1 ),
    inference(superposition,[],[f47,f37])).

fof(f91,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f86,f47])).

fof(f86,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f29,f49,f45])).

fof(f29,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f52,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f30,f49,f45])).

fof(f30,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (6097)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (6112)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (6105)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (6088)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (6104)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (6087)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (6096)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (6086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (6089)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (6085)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (6112)Refutation not found, incomplete strategy% (6112)------------------------------
% 0.21/0.53  % (6112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6112)Memory used [KB]: 1663
% 0.21/0.53  % (6112)Time elapsed: 0.124 s
% 0.21/0.53  % (6112)------------------------------
% 0.21/0.53  % (6112)------------------------------
% 0.21/0.53  % (6095)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (6084)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (6084)Refutation not found, incomplete strategy% (6084)------------------------------
% 0.21/0.53  % (6084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6084)Memory used [KB]: 1663
% 0.21/0.53  % (6084)Time elapsed: 0.124 s
% 0.21/0.53  % (6084)------------------------------
% 0.21/0.53  % (6084)------------------------------
% 0.21/0.53  % (6106)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (6083)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (6107)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (6091)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (6099)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (6111)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (6099)Refutation not found, incomplete strategy% (6099)------------------------------
% 0.21/0.54  % (6099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6108)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (6111)Refutation not found, incomplete strategy% (6111)------------------------------
% 0.21/0.54  % (6111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6111)Memory used [KB]: 10746
% 0.21/0.54  % (6111)Time elapsed: 0.141 s
% 0.21/0.54  % (6111)------------------------------
% 0.21/0.54  % (6111)------------------------------
% 0.21/0.54  % (6109)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (6110)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (6103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (6098)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (6099)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6099)Memory used [KB]: 10618
% 0.21/0.54  % (6099)Time elapsed: 0.140 s
% 0.21/0.54  % (6099)------------------------------
% 0.21/0.54  % (6099)------------------------------
% 0.21/0.54  % (6100)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (6101)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (6102)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (6090)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (6092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (6095)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f52,f53,f150,f173,f197,f232])).
% 0.21/0.55  fof(f232,plain,(
% 0.21/0.55    spl3_1 | spl3_2 | ~spl3_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    $false | (spl3_1 | spl3_2 | ~spl3_4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f230,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0) | spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    spl3_2 <=> r2_hidden(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    r2_hidden(sK1,sK0) | (spl3_1 | ~spl3_4)),
% 0.21/0.55    inference(forward_demodulation,[],[f229,f149])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    sK1 = sK2(sK0,k1_tarski(sK1),sK0) | ~spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f147])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    spl3_4 <=> sK1 = sK2(sK0,k1_tarski(sK1),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f228])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 0.21/0.55    inference(equality_resolution,[],[f201])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    ( ! [X0] : (sK0 != X0 | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0)) ) | spl3_1),
% 0.21/0.55    inference(superposition,[],[f47,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    spl3_1 <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    ~spl3_1 | ~spl3_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f196])).
% 0.21/0.55  fof(f196,plain,(
% 0.21/0.55    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f188,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    r2_hidden(sK1,sK0) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f49])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0) | ~spl3_1),
% 0.21/0.55    inference(superposition,[],[f40,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl3_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f45])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.55    inference(equality_resolution,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.55    inference(nnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    spl3_1 | ~spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f172,f144,f45])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    spl3_3 <=> ! [X0] : ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),X0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl3_3),
% 0.21/0.55    inference(subsumption_resolution,[],[f159,f145])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),X0)) ) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f144])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | ~spl3_3),
% 0.21/0.55    inference(resolution,[],[f145,f37])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    spl3_3 | spl3_4 | spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f135,f45,f147,f144])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X0] : (sK1 = sK2(sK0,k1_tarski(sK1),sK0) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),X0)) ) | spl3_1),
% 0.21/0.55    inference(resolution,[],[f95,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k4_xboole_0(X0,k1_tarski(sK1)))) ) | spl3_1),
% 0.21/0.55    inference(resolution,[],[f92,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | spl3_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f91,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 0.21/0.55    inference(equality_resolution,[],[f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0] : (sK0 != X0 | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0)) ) | spl3_1),
% 0.21/0.55    inference(superposition,[],[f47,f37])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f86,f47])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 0.21/0.55    inference(resolution,[],[f85,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    spl3_1 | ~spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f29,f49,f45])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f16])).
% 0.21/0.55  fof(f16,conjecture,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ~spl3_1 | spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f30,f49,f45])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (6095)------------------------------
% 0.21/0.55  % (6095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6095)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (6095)Memory used [KB]: 10746
% 0.21/0.55  % (6095)Time elapsed: 0.156 s
% 0.21/0.55  % (6095)------------------------------
% 0.21/0.55  % (6095)------------------------------
% 0.21/0.55  % (6078)Success in time 0.194 s
%------------------------------------------------------------------------------
