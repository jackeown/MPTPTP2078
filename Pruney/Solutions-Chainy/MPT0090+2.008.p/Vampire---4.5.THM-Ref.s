%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 177 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 (1074 expanded)
%              Number of equality atoms :   41 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f45,f61,f248])).

fof(f248,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f225,f115])).

fof(f115,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,sK1,sK0),k4_xboole_0(X0,sK1))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f101,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f101,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f100,f97])).

fof(f97,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK2(sK0,sK1,X0),sK0)
        | r2_hidden(sK2(sK0,sK1,X0),X0) )
    | spl3_2 ),
    inference(superposition,[],[f43,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f100,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,
    ( ! [X2] :
        ( sK0 != X2
        | r2_hidden(sK2(sK0,sK1,X2),sK1)
        | ~ r2_hidden(sK2(sK0,sK1,X2),sK0)
        | ~ r2_hidden(sK2(sK0,sK1,X2),X2) )
    | spl3_2 ),
    inference(superposition,[],[f43,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f225,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f140,f175,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f175,plain,
    ( ! [X4] : ~ r2_hidden(X4,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f171,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f171,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(X4,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) )
    | ~ spl3_1 ),
    inference(superposition,[],[f34,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f74,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f21,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f38,f32])).

fof(f38,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f21,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f140,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f97,f115,f80])).

fof(f80,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | r2_hidden(X3,k4_xboole_0(sK0,sK1))
        | ~ r2_hidden(X3,sK0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f33,f62])).

fof(f61,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f51,f39])).

fof(f39,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f51,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f21,f42])).

fof(f42,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f45,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f18,f41,f37])).

fof(f18,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK0 != k4_xboole_0(sK0,sK1)
        | ~ r1_xboole_0(sK0,sK1) )
      & ( sK0 = k4_xboole_0(sK0,sK1)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f41,f37])).

fof(f19,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:11:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (4303)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (4318)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (4304)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (4311)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (4307)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (4313)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (4312)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (4311)Refutation not found, incomplete strategy% (4311)------------------------------
% 0.22/0.52  % (4311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4311)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4311)Memory used [KB]: 10618
% 0.22/0.52  % (4311)Time elapsed: 0.116 s
% 0.22/0.52  % (4311)------------------------------
% 0.22/0.52  % (4311)------------------------------
% 0.22/0.52  % (4318)Refutation not found, incomplete strategy% (4318)------------------------------
% 0.22/0.52  % (4318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4318)Memory used [KB]: 10618
% 0.22/0.52  % (4318)Time elapsed: 0.114 s
% 0.22/0.52  % (4318)------------------------------
% 0.22/0.52  % (4318)------------------------------
% 0.22/0.53  % (4302)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (4301)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (4301)Refutation not found, incomplete strategy% (4301)------------------------------
% 0.22/0.54  % (4301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4301)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4301)Memory used [KB]: 1663
% 0.22/0.54  % (4301)Time elapsed: 0.126 s
% 0.22/0.54  % (4301)------------------------------
% 0.22/0.54  % (4301)------------------------------
% 0.22/0.54  % (4306)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (4306)Refutation not found, incomplete strategy% (4306)------------------------------
% 0.22/0.54  % (4306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4306)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4306)Memory used [KB]: 6140
% 0.22/0.54  % (4306)Time elapsed: 0.129 s
% 0.22/0.54  % (4306)------------------------------
% 0.22/0.54  % (4306)------------------------------
% 0.22/0.54  % (4305)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (4324)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (4330)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (4305)Refutation not found, incomplete strategy% (4305)------------------------------
% 0.22/0.54  % (4305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4305)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4305)Memory used [KB]: 6140
% 0.22/0.54  % (4305)Time elapsed: 0.127 s
% 0.22/0.54  % (4305)------------------------------
% 0.22/0.54  % (4305)------------------------------
% 0.22/0.54  % (4312)Refutation not found, incomplete strategy% (4312)------------------------------
% 0.22/0.54  % (4312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4312)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4312)Memory used [KB]: 10618
% 0.22/0.54  % (4312)Time elapsed: 0.136 s
% 0.22/0.54  % (4312)------------------------------
% 0.22/0.54  % (4312)------------------------------
% 0.22/0.54  % (4325)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (4327)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (4326)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (4316)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (4316)Refutation not found, incomplete strategy% (4316)------------------------------
% 0.22/0.55  % (4316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4316)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4316)Memory used [KB]: 6140
% 0.22/0.55  % (4316)Time elapsed: 0.002 s
% 0.22/0.55  % (4316)------------------------------
% 0.22/0.55  % (4316)------------------------------
% 0.22/0.55  % (4329)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (4309)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (4317)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (4320)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (4319)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (4322)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (4322)Refutation not found, incomplete strategy% (4322)------------------------------
% 0.22/0.55  % (4322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4322)Memory used [KB]: 1663
% 0.22/0.55  % (4322)Time elapsed: 0.150 s
% 0.22/0.55  % (4322)------------------------------
% 0.22/0.55  % (4322)------------------------------
% 0.22/0.55  % (4321)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (4314)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (4321)Refutation not found, incomplete strategy% (4321)------------------------------
% 0.22/0.56  % (4321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4321)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4321)Memory used [KB]: 10618
% 0.22/0.56  % (4321)Time elapsed: 0.150 s
% 0.22/0.56  % (4321)------------------------------
% 0.22/0.56  % (4321)------------------------------
% 0.22/0.56  % (4328)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (4323)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (4310)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (4327)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f250,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f44,f45,f61,f248])).
% 0.22/0.57  fof(f248,plain,(
% 0.22/0.57    ~spl3_1 | spl3_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f247])).
% 0.22/0.57  fof(f247,plain,(
% 0.22/0.57    $false | (~spl3_1 | spl3_2)),
% 0.22/0.57    inference(subsumption_resolution,[],[f225,f115])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ( ! [X0] : (~r2_hidden(sK2(sK0,sK1,sK0),k4_xboole_0(X0,sK1))) ) | spl3_2),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f101,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(flattening,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    r2_hidden(sK2(sK0,sK1,sK0),sK1) | spl3_2),
% 0.22/0.57    inference(subsumption_resolution,[],[f100,f97])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f96])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    r2_hidden(sK2(sK0,sK1,sK0),sK0) | r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 0.22/0.57    inference(equality_resolution,[],[f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X0] : (sK0 != X0 | r2_hidden(sK2(sK0,sK1,X0),sK0) | r2_hidden(sK2(sK0,sK1,X0),X0)) ) | spl3_2),
% 0.22/0.57    inference(superposition,[],[f43,f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    sK0 != k4_xboole_0(sK0,sK1) | spl3_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    spl3_2 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    r2_hidden(sK2(sK0,sK1,sK0),sK1) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    r2_hidden(sK2(sK0,sK1,sK0),sK1) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 0.22/0.57    inference(equality_resolution,[],[f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ( ! [X2] : (sK0 != X2 | r2_hidden(sK2(sK0,sK1,X2),sK1) | ~r2_hidden(sK2(sK0,sK1,X2),sK0) | ~r2_hidden(sK2(sK0,sK1,X2),X2)) ) | spl3_2),
% 0.22/0.57    inference(superposition,[],[f43,f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f225,plain,(
% 0.22/0.57    r2_hidden(sK2(sK0,sK1,sK0),k4_xboole_0(sK0,sK1)) | (~spl3_1 | spl3_2)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f140,f175,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f175,plain,(
% 0.22/0.57    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))) ) | ~spl3_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f171,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f171,plain,(
% 0.22/0.57    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))) ) | ~spl3_1),
% 0.22/0.57    inference(superposition,[],[f34,f102])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f74,f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.22/0.57    inference(superposition,[],[f21,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f38,f32])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.57  fof(f140,plain,(
% 0.22/0.57    r2_hidden(sK2(sK0,sK1,sK0),k1_xboole_0) | (~spl3_1 | spl3_2)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f97,f115,f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,k4_xboole_0(sK0,sK1)) | ~r2_hidden(X3,sK0)) ) | ~spl3_1),
% 0.22/0.57    inference(superposition,[],[f33,f62])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    spl3_1 | ~spl3_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    $false | (spl3_1 | ~spl3_2)),
% 0.22/0.57    inference(subsumption_resolution,[],[f51,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f37])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 0.22/0.57    inference(superposition,[],[f21,f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f41])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    spl3_1 | spl3_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f18,f41,f37])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.22/0.57  fof(f10,plain,(
% 0.22/0.57    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f9,plain,(
% 0.22/0.57    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,plain,(
% 0.22/0.57    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.57    inference(negated_conjecture,[],[f6])).
% 0.22/0.57  fof(f6,conjecture,(
% 0.22/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ~spl3_1 | ~spl3_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f19,f41,f37])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f11])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (4327)------------------------------
% 0.22/0.57  % (4327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (4327)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (4327)Memory used [KB]: 10874
% 0.22/0.57  % (4327)Time elapsed: 0.171 s
% 0.22/0.57  % (4327)------------------------------
% 0.22/0.57  % (4327)------------------------------
% 0.22/0.57  % (4300)Success in time 0.206 s
%------------------------------------------------------------------------------
