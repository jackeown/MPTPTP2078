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
% DateTime   : Thu Dec  3 12:31:30 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 127 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 ( 420 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4464,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f170,f209,f4463])).

fof(f4463,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f4462])).

fof(f4462,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f4446,f30])).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4446,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_2 ),
    inference(resolution,[],[f4329,f35])).

fof(f35,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f4329,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(X9,k4_xboole_0(X10,X11))
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f352,f738])).

fof(f738,plain,(
    ! [X6,X7,X5] : r1_xboole_0(X5,k4_xboole_0(X6,k2_xboole_0(X7,X6))) ),
    inference(resolution,[],[f180,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) ),
    inference(resolution,[],[f26,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f180,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(k4_xboole_0(X3,X4),X3)
      | r1_xboole_0(X5,k4_xboole_0(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f173,f18])).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(k4_xboole_0(X3,X4),X4)
      | ~ r1_xboole_0(k4_xboole_0(X3,X4),X3)
      | r1_xboole_0(X5,k4_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f78,f93])).

fof(f93,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f48,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f48,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f22,f21])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X17,X18,X16] :
      ( r1_xboole_0(X16,k4_xboole_0(X17,X18))
      | ~ r1_xboole_0(X16,X18)
      | ~ r1_xboole_0(X16,X17) ) ),
    inference(resolution,[],[f41,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X2,k2_xboole_0(X0,X1))
      | r1_xboole_0(X2,k4_xboole_0(X1,X0)) ) ),
    inference(superposition,[],[f26,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f352,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_xboole_0(X8,k4_xboole_0(X10,k2_xboole_0(X11,X9)))
      | ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X8,k4_xboole_0(X10,X11)) ) ),
    inference(resolution,[],[f99,f26])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X3,X0)
      | ~ r1_xboole_0(X3,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ) ),
    inference(superposition,[],[f24,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f19,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f209,plain,
    ( ~ spl4_4
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f179,f33,f28,f206])).

fof(f206,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f179,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f171,f30])).

fof(f171,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | spl4_2 ),
    inference(resolution,[],[f78,f35])).

fof(f170,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f146,f28,f167])).

fof(f167,plain,
    ( spl4_3
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f146,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f94,f30])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f48,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f31,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (13453)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (13454)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (13458)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (13464)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.45  % (13457)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.46  % (13459)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (13461)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.48  % (13456)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.48  % (13463)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.48  % (13455)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.49  % (13460)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.49  % (13462)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.53  % (13461)Refutation not found, incomplete strategy% (13461)------------------------------
% 0.21/0.53  % (13461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13461)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13461)Memory used [KB]: 6012
% 0.21/0.54  % (13461)Time elapsed: 0.077 s
% 0.21/0.54  % (13461)------------------------------
% 0.21/0.54  % (13461)------------------------------
% 2.70/0.73  % (13459)Refutation found. Thanks to Tanya!
% 2.70/0.73  % SZS status Theorem for theBenchmark
% 2.70/0.73  % SZS output start Proof for theBenchmark
% 2.70/0.73  fof(f4464,plain,(
% 2.70/0.73    $false),
% 2.70/0.73    inference(avatar_sat_refutation,[],[f31,f36,f170,f209,f4463])).
% 2.70/0.73  fof(f4463,plain,(
% 2.70/0.73    ~spl4_1 | spl4_2),
% 2.70/0.73    inference(avatar_contradiction_clause,[],[f4462])).
% 2.70/0.73  fof(f4462,plain,(
% 2.70/0.73    $false | (~spl4_1 | spl4_2)),
% 2.70/0.73    inference(subsumption_resolution,[],[f4446,f30])).
% 2.70/0.73  fof(f30,plain,(
% 2.70/0.73    r1_xboole_0(sK0,sK1) | ~spl4_1),
% 2.70/0.73    inference(avatar_component_clause,[],[f28])).
% 2.70/0.73  fof(f28,plain,(
% 2.70/0.73    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 2.70/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.70/0.73  fof(f4446,plain,(
% 2.70/0.73    ~r1_xboole_0(sK0,sK1) | spl4_2),
% 2.70/0.73    inference(resolution,[],[f4329,f35])).
% 2.70/0.73  fof(f35,plain,(
% 2.70/0.73    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl4_2),
% 2.70/0.73    inference(avatar_component_clause,[],[f33])).
% 2.70/0.73  fof(f33,plain,(
% 2.70/0.73    spl4_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.70/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.70/0.73  fof(f4329,plain,(
% 2.70/0.73    ( ! [X10,X11,X9] : (r1_xboole_0(X9,k4_xboole_0(X10,X11)) | ~r1_xboole_0(X9,X10)) )),
% 2.70/0.73    inference(resolution,[],[f352,f738])).
% 2.70/0.73  fof(f738,plain,(
% 2.70/0.73    ( ! [X6,X7,X5] : (r1_xboole_0(X5,k4_xboole_0(X6,k2_xboole_0(X7,X6)))) )),
% 2.70/0.73    inference(resolution,[],[f180,f39])).
% 2.70/0.73  fof(f39,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2)) )),
% 2.70/0.73    inference(resolution,[],[f26,f18])).
% 2.70/0.73  fof(f18,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f5])).
% 2.70/0.73  fof(f5,axiom,(
% 2.70/0.73    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.70/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.70/0.73  fof(f26,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f11])).
% 2.70/0.73  fof(f11,plain,(
% 2.70/0.73    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.70/0.73    inference(ennf_transformation,[],[f4])).
% 2.70/0.73  fof(f4,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.70/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.70/0.73  fof(f180,plain,(
% 2.70/0.73    ( ! [X4,X5,X3] : (~r1_xboole_0(k4_xboole_0(X3,X4),X3) | r1_xboole_0(X5,k4_xboole_0(X3,X4))) )),
% 2.70/0.73    inference(subsumption_resolution,[],[f173,f18])).
% 2.70/0.73  fof(f173,plain,(
% 2.70/0.73    ( ! [X4,X5,X3] : (~r1_xboole_0(k4_xboole_0(X3,X4),X4) | ~r1_xboole_0(k4_xboole_0(X3,X4),X3) | r1_xboole_0(X5,k4_xboole_0(X3,X4))) )),
% 2.70/0.73    inference(resolution,[],[f78,f93])).
% 2.70/0.73  fof(f93,plain,(
% 2.70/0.73    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2)) )),
% 2.70/0.73    inference(duplicate_literal_removal,[],[f92])).
% 2.70/0.73  fof(f92,plain,(
% 2.70/0.73    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 2.70/0.73    inference(resolution,[],[f48,f21])).
% 2.70/0.73  fof(f21,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f15])).
% 2.70/0.73  fof(f15,plain,(
% 2.70/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.70/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).
% 2.70/0.73  fof(f14,plain,(
% 2.70/0.73    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.70/0.73    introduced(choice_axiom,[])).
% 2.70/0.73  fof(f10,plain,(
% 2.70/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.70/0.73    inference(ennf_transformation,[],[f8])).
% 2.70/0.73  fof(f8,plain,(
% 2.70/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.70/0.73    inference(rectify,[],[f1])).
% 2.70/0.73  fof(f1,axiom,(
% 2.70/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.70/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.70/0.73  fof(f48,plain,(
% 2.70/0.73    ( ! [X4,X5,X3] : (~r2_hidden(sK3(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4)) )),
% 2.70/0.73    inference(resolution,[],[f22,f21])).
% 2.70/0.73  fof(f22,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f15])).
% 2.70/0.73  fof(f78,plain,(
% 2.70/0.73    ( ! [X17,X18,X16] : (r1_xboole_0(X16,k4_xboole_0(X17,X18)) | ~r1_xboole_0(X16,X18) | ~r1_xboole_0(X16,X17)) )),
% 2.70/0.73    inference(resolution,[],[f41,f24])).
% 2.70/0.73  fof(f24,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f11])).
% 2.70/0.73  fof(f41,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k2_xboole_0(X0,X1)) | r1_xboole_0(X2,k4_xboole_0(X1,X0))) )),
% 2.70/0.73    inference(superposition,[],[f26,f19])).
% 2.70/0.73  fof(f19,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f2])).
% 2.70/0.73  fof(f2,axiom,(
% 2.70/0.73    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.70/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.70/0.73  fof(f352,plain,(
% 2.70/0.73    ( ! [X10,X8,X11,X9] : (~r1_xboole_0(X8,k4_xboole_0(X10,k2_xboole_0(X11,X9))) | ~r1_xboole_0(X8,X9) | r1_xboole_0(X8,k4_xboole_0(X10,X11))) )),
% 2.70/0.73    inference(resolution,[],[f99,f26])).
% 2.70/0.73  fof(f99,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X3,k2_xboole_0(X0,k4_xboole_0(X1,X2))) | ~r1_xboole_0(X3,X0) | ~r1_xboole_0(X3,k4_xboole_0(X1,k2_xboole_0(X2,X0)))) )),
% 2.70/0.73    inference(superposition,[],[f24,f54])).
% 2.70/0.73  fof(f54,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 2.70/0.73    inference(superposition,[],[f19,f23])).
% 2.70/0.73  fof(f23,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f3])).
% 2.70/0.73  fof(f3,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.70/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.70/0.73  fof(f209,plain,(
% 2.70/0.73    ~spl4_4 | ~spl4_1 | spl4_2),
% 2.70/0.73    inference(avatar_split_clause,[],[f179,f33,f28,f206])).
% 2.70/0.73  fof(f206,plain,(
% 2.70/0.73    spl4_4 <=> r1_xboole_0(sK0,sK2)),
% 2.70/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.70/0.73  fof(f179,plain,(
% 2.70/0.73    ~r1_xboole_0(sK0,sK2) | (~spl4_1 | spl4_2)),
% 2.70/0.73    inference(subsumption_resolution,[],[f171,f30])).
% 2.70/0.73  fof(f171,plain,(
% 2.70/0.73    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | spl4_2),
% 2.70/0.73    inference(resolution,[],[f78,f35])).
% 2.70/0.73  fof(f170,plain,(
% 2.70/0.73    spl4_3 | ~spl4_1),
% 2.70/0.73    inference(avatar_split_clause,[],[f146,f28,f167])).
% 2.70/0.73  fof(f167,plain,(
% 2.70/0.73    spl4_3 <=> r1_xboole_0(sK1,sK0)),
% 2.70/0.73    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.70/0.73  fof(f146,plain,(
% 2.70/0.73    r1_xboole_0(sK1,sK0) | ~spl4_1),
% 2.70/0.73    inference(resolution,[],[f94,f30])).
% 2.70/0.73  fof(f94,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.70/0.73    inference(duplicate_literal_removal,[],[f91])).
% 2.70/0.73  fof(f91,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) | r1_xboole_0(X1,X0)) )),
% 2.70/0.73    inference(resolution,[],[f48,f20])).
% 2.70/0.73  fof(f20,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f15])).
% 2.70/0.73  fof(f36,plain,(
% 2.70/0.73    ~spl4_2),
% 2.70/0.73    inference(avatar_split_clause,[],[f17,f33])).
% 2.70/0.73  fof(f17,plain,(
% 2.70/0.73    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 2.70/0.73    inference(cnf_transformation,[],[f13])).
% 2.70/0.73  fof(f13,plain,(
% 2.70/0.73    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 2.70/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 2.70/0.73  fof(f12,plain,(
% 2.70/0.73    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 2.70/0.73    introduced(choice_axiom,[])).
% 2.70/0.73  fof(f9,plain,(
% 2.70/0.73    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 2.70/0.73    inference(ennf_transformation,[],[f7])).
% 2.70/0.73  fof(f7,negated_conjecture,(
% 2.70/0.73    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.70/0.73    inference(negated_conjecture,[],[f6])).
% 2.70/0.73  fof(f6,conjecture,(
% 2.70/0.73    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 2.70/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).
% 2.70/0.73  fof(f31,plain,(
% 2.70/0.73    spl4_1),
% 2.70/0.73    inference(avatar_split_clause,[],[f16,f28])).
% 2.70/0.73  fof(f16,plain,(
% 2.70/0.73    r1_xboole_0(sK0,sK1)),
% 2.70/0.73    inference(cnf_transformation,[],[f13])).
% 2.70/0.73  % SZS output end Proof for theBenchmark
% 2.70/0.73  % (13459)------------------------------
% 2.70/0.73  % (13459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.73  % (13459)Termination reason: Refutation
% 2.70/0.73  
% 2.70/0.73  % (13459)Memory used [KB]: 10490
% 2.70/0.73  % (13459)Time elapsed: 0.275 s
% 2.70/0.73  % (13459)------------------------------
% 2.70/0.73  % (13459)------------------------------
% 2.70/0.73  % (13452)Success in time 0.359 s
%------------------------------------------------------------------------------
