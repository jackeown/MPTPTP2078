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
% DateTime   : Thu Dec  3 12:31:36 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 156 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  210 ( 711 expanded)
%              Number of equality atoms :   42 ( 146 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f919,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f54,f73,f916])).

fof(f916,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f915])).

fof(f915,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f406,f810])).

fof(f810,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f808])).

fof(f808,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(X4,k1_xboole_0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f43,f446])).

fof(f446,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f440,f435])).

fof(f435,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f26,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f89,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f89,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f26,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f47,f41])).

fof(f47,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f440,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f41,f115])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f406,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f110,f133,f95])).

fof(f95,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | r2_hidden(X3,k4_xboole_0(sK0,sK1))
        | ~ r2_hidden(X3,sK0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f42,f74])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f133,plain,
    ( ! [X0] : ~ r2_hidden(sK2(sK0,sK1,sK0),k4_xboole_0(X0,sK1))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f114,f43])).

fof(f114,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f113,f110])).

fof(f113,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,
    ( ! [X2] :
        ( sK0 != X2
        | r2_hidden(sK2(sK0,sK1,X2),sK1)
        | ~ r2_hidden(sK2(sK0,sK1,X2),sK0)
        | ~ r2_hidden(sK2(sK0,sK1,X2),X2) )
    | spl3_2 ),
    inference(superposition,[],[f52,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_2
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f110,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK2(sK0,sK1,X0),sK0)
        | r2_hidden(sK2(sK0,sK1,X0),X0) )
    | spl3_2 ),
    inference(superposition,[],[f52,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f63,f48])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f63,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f26,f51])).

fof(f51,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f54,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f23,f50,f46])).

fof(f23,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
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

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f53,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f50,f46])).

fof(f24,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (29344)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.47  % (29344)Refutation not found, incomplete strategy% (29344)------------------------------
% 0.20/0.47  % (29344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29352)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.48  % (29344)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (29344)Memory used [KB]: 1663
% 0.20/0.48  % (29344)Time elapsed: 0.052 s
% 0.20/0.48  % (29344)------------------------------
% 0.20/0.48  % (29344)------------------------------
% 0.20/0.50  % (29351)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (29367)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (29348)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (29348)Refutation not found, incomplete strategy% (29348)------------------------------
% 0.20/0.51  % (29348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29348)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29348)Memory used [KB]: 6268
% 0.20/0.51  % (29348)Time elapsed: 0.110 s
% 0.20/0.51  % (29348)------------------------------
% 0.20/0.51  % (29348)------------------------------
% 0.20/0.51  % (29349)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (29353)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (29354)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (29355)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (29354)Refutation not found, incomplete strategy% (29354)------------------------------
% 0.20/0.52  % (29354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29354)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29354)Memory used [KB]: 10618
% 0.20/0.52  % (29354)Time elapsed: 0.107 s
% 0.20/0.52  % (29354)------------------------------
% 0.20/0.52  % (29354)------------------------------
% 0.20/0.52  % (29359)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (29359)Refutation not found, incomplete strategy% (29359)------------------------------
% 0.20/0.52  % (29359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29359)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29359)Memory used [KB]: 6140
% 0.20/0.52  % (29359)Time elapsed: 0.002 s
% 0.20/0.52  % (29359)------------------------------
% 0.20/0.52  % (29359)------------------------------
% 0.20/0.52  % (29364)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.53  % (29356)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.53  % (29347)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.53  % (29345)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.53  % (29346)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (29372)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (29353)Refutation not found, incomplete strategy% (29353)------------------------------
% 1.36/0.54  % (29353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (29353)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (29353)Memory used [KB]: 10618
% 1.36/0.54  % (29353)Time elapsed: 0.127 s
% 1.36/0.54  % (29353)------------------------------
% 1.36/0.54  % (29353)------------------------------
% 1.36/0.54  % (29355)Refutation not found, incomplete strategy% (29355)------------------------------
% 1.36/0.54  % (29355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (29355)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (29355)Memory used [KB]: 10618
% 1.36/0.54  % (29355)Time elapsed: 0.127 s
% 1.36/0.54  % (29355)------------------------------
% 1.36/0.54  % (29355)------------------------------
% 1.36/0.54  % (29370)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (29369)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (29373)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (29371)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (29364)Refutation not found, incomplete strategy% (29364)------------------------------
% 1.36/0.54  % (29364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (29364)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (29364)Memory used [KB]: 10746
% 1.36/0.54  % (29364)Time elapsed: 0.126 s
% 1.36/0.54  % (29364)------------------------------
% 1.36/0.54  % (29364)------------------------------
% 1.36/0.55  % (29365)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (29362)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  % (29363)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (29361)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (29365)Refutation not found, incomplete strategy% (29365)------------------------------
% 1.36/0.55  % (29365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (29365)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (29365)Memory used [KB]: 1663
% 1.36/0.55  % (29365)Time elapsed: 0.140 s
% 1.36/0.55  % (29365)------------------------------
% 1.36/0.55  % (29365)------------------------------
% 1.36/0.55  % (29361)Refutation not found, incomplete strategy% (29361)------------------------------
% 1.36/0.55  % (29361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (29361)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (29361)Memory used [KB]: 10618
% 1.36/0.55  % (29361)Time elapsed: 0.140 s
% 1.36/0.55  % (29361)------------------------------
% 1.36/0.55  % (29361)------------------------------
% 1.48/0.55  % (29357)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (29374)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.48/0.56  % (29374)Refutation not found, incomplete strategy% (29374)------------------------------
% 1.48/0.56  % (29374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (29374)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (29374)Memory used [KB]: 6140
% 1.48/0.56  % (29374)Time elapsed: 0.004 s
% 1.48/0.56  % (29374)------------------------------
% 1.48/0.56  % (29374)------------------------------
% 1.48/0.57  % (29360)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.57  % (29366)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.48/0.57  % (29366)Refutation not found, incomplete strategy% (29366)------------------------------
% 1.48/0.57  % (29366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (29366)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (29366)Memory used [KB]: 10618
% 1.48/0.57  % (29366)Time elapsed: 0.135 s
% 1.48/0.57  % (29366)------------------------------
% 1.48/0.57  % (29366)------------------------------
% 1.48/0.57  % (29350)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.58  % (29358)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.59  % (29368)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.62  % (29370)Refutation found. Thanks to Tanya!
% 1.48/0.62  % SZS status Theorem for theBenchmark
% 1.48/0.62  % SZS output start Proof for theBenchmark
% 1.48/0.62  fof(f919,plain,(
% 1.48/0.62    $false),
% 1.48/0.62    inference(avatar_sat_refutation,[],[f53,f54,f73,f916])).
% 1.48/0.62  fof(f916,plain,(
% 1.48/0.62    ~spl3_1 | spl3_2),
% 1.48/0.62    inference(avatar_contradiction_clause,[],[f915])).
% 1.48/0.62  fof(f915,plain,(
% 1.48/0.62    $false | (~spl3_1 | spl3_2)),
% 1.48/0.62    inference(subsumption_resolution,[],[f406,f810])).
% 1.48/0.62  fof(f810,plain,(
% 1.48/0.62    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl3_1),
% 1.48/0.62    inference(duplicate_literal_removal,[],[f808])).
% 1.48/0.62  fof(f808,plain,(
% 1.48/0.62    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0)) ) | ~spl3_1),
% 1.48/0.62    inference(superposition,[],[f43,f446])).
% 1.48/0.62  fof(f446,plain,(
% 1.48/0.62    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_1),
% 1.48/0.62    inference(subsumption_resolution,[],[f440,f435])).
% 1.48/0.62  fof(f435,plain,(
% 1.48/0.62    r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 1.48/0.62    inference(superposition,[],[f26,f115])).
% 1.48/0.62  fof(f115,plain,(
% 1.48/0.62    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 1.48/0.62    inference(unit_resulting_resolution,[],[f89,f41])).
% 1.48/0.62  fof(f41,plain,(
% 1.48/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.62    inference(definition_unfolding,[],[f30,f28])).
% 1.48/0.62  fof(f28,plain,(
% 1.48/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.48/0.62    inference(cnf_transformation,[],[f7])).
% 1.48/0.62  fof(f7,axiom,(
% 1.48/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.48/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.48/0.62  fof(f30,plain,(
% 1.48/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.62    inference(cnf_transformation,[],[f17])).
% 1.48/0.62  fof(f17,plain,(
% 1.48/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.48/0.62    inference(nnf_transformation,[],[f3])).
% 1.48/0.62  fof(f3,axiom,(
% 1.48/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.48/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.48/0.62  fof(f89,plain,(
% 1.48/0.62    r1_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 1.48/0.62    inference(superposition,[],[f26,f74])).
% 1.48/0.62  fof(f74,plain,(
% 1.48/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 1.48/0.62    inference(unit_resulting_resolution,[],[f47,f41])).
% 1.48/0.62  fof(f47,plain,(
% 1.48/0.62    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 1.48/0.62    inference(avatar_component_clause,[],[f46])).
% 1.48/0.62  fof(f46,plain,(
% 1.48/0.62    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 1.48/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.48/0.62  fof(f26,plain,(
% 1.48/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.48/0.62    inference(cnf_transformation,[],[f8])).
% 1.48/0.62  fof(f8,axiom,(
% 1.48/0.62    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.48/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.48/0.62  fof(f440,plain,(
% 1.48/0.62    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | ~spl3_1),
% 1.48/0.62    inference(superposition,[],[f41,f115])).
% 1.48/0.62  fof(f43,plain,(
% 1.48/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.48/0.62    inference(equality_resolution,[],[f33])).
% 1.48/0.62  fof(f33,plain,(
% 1.48/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.48/0.62    inference(cnf_transformation,[],[f22])).
% 1.48/0.62  fof(f22,plain,(
% 1.48/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.48/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 1.48/0.62  fof(f21,plain,(
% 1.48/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.48/0.62    introduced(choice_axiom,[])).
% 1.48/0.62  fof(f20,plain,(
% 1.48/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.48/0.62    inference(rectify,[],[f19])).
% 1.48/0.62  fof(f19,plain,(
% 1.48/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.48/0.62    inference(flattening,[],[f18])).
% 1.48/0.62  fof(f18,plain,(
% 1.48/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.48/0.62    inference(nnf_transformation,[],[f2])).
% 1.48/0.62  fof(f2,axiom,(
% 1.48/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.48/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.48/0.62  fof(f406,plain,(
% 1.48/0.62    r2_hidden(sK2(sK0,sK1,sK0),k1_xboole_0) | (~spl3_1 | spl3_2)),
% 1.48/0.62    inference(unit_resulting_resolution,[],[f110,f133,f95])).
% 1.48/0.62  fof(f95,plain,(
% 1.48/0.62    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,k4_xboole_0(sK0,sK1)) | ~r2_hidden(X3,sK0)) ) | ~spl3_1),
% 1.48/0.62    inference(superposition,[],[f42,f74])).
% 1.48/0.62  fof(f42,plain,(
% 1.48/0.62    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.48/0.62    inference(equality_resolution,[],[f34])).
% 1.48/0.62  fof(f34,plain,(
% 1.48/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.48/0.62    inference(cnf_transformation,[],[f22])).
% 1.48/0.62  fof(f133,plain,(
% 1.48/0.62    ( ! [X0] : (~r2_hidden(sK2(sK0,sK1,sK0),k4_xboole_0(X0,sK1))) ) | spl3_2),
% 1.48/0.62    inference(unit_resulting_resolution,[],[f114,f43])).
% 1.48/0.62  fof(f114,plain,(
% 1.48/0.62    r2_hidden(sK2(sK0,sK1,sK0),sK1) | spl3_2),
% 1.48/0.62    inference(subsumption_resolution,[],[f113,f110])).
% 1.48/0.62  fof(f113,plain,(
% 1.48/0.62    r2_hidden(sK2(sK0,sK1,sK0),sK1) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 1.48/0.62    inference(duplicate_literal_removal,[],[f112])).
% 1.48/0.62  fof(f112,plain,(
% 1.48/0.62    r2_hidden(sK2(sK0,sK1,sK0),sK1) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 1.48/0.62    inference(equality_resolution,[],[f78])).
% 1.48/0.62  fof(f78,plain,(
% 1.48/0.62    ( ! [X2] : (sK0 != X2 | r2_hidden(sK2(sK0,sK1,X2),sK1) | ~r2_hidden(sK2(sK0,sK1,X2),sK0) | ~r2_hidden(sK2(sK0,sK1,X2),X2)) ) | spl3_2),
% 1.48/0.62    inference(superposition,[],[f52,f37])).
% 1.48/0.62  fof(f37,plain,(
% 1.48/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.48/0.62    inference(cnf_transformation,[],[f22])).
% 1.48/0.62  fof(f52,plain,(
% 1.48/0.62    sK0 != k4_xboole_0(sK0,sK1) | spl3_2),
% 1.48/0.62    inference(avatar_component_clause,[],[f50])).
% 1.48/0.62  fof(f50,plain,(
% 1.48/0.62    spl3_2 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 1.48/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.48/0.62  fof(f110,plain,(
% 1.48/0.62    r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 1.48/0.62    inference(duplicate_literal_removal,[],[f109])).
% 1.48/0.62  fof(f109,plain,(
% 1.48/0.62    r2_hidden(sK2(sK0,sK1,sK0),sK0) | r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl3_2),
% 1.48/0.62    inference(equality_resolution,[],[f76])).
% 1.48/0.62  fof(f76,plain,(
% 1.48/0.62    ( ! [X0] : (sK0 != X0 | r2_hidden(sK2(sK0,sK1,X0),sK0) | r2_hidden(sK2(sK0,sK1,X0),X0)) ) | spl3_2),
% 1.48/0.62    inference(superposition,[],[f52,f35])).
% 1.48/0.62  fof(f35,plain,(
% 1.48/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.48/0.62    inference(cnf_transformation,[],[f22])).
% 1.48/0.62  fof(f73,plain,(
% 1.48/0.62    spl3_1 | ~spl3_2),
% 1.48/0.62    inference(avatar_contradiction_clause,[],[f72])).
% 1.48/0.62  fof(f72,plain,(
% 1.48/0.62    $false | (spl3_1 | ~spl3_2)),
% 1.48/0.62    inference(subsumption_resolution,[],[f63,f48])).
% 1.48/0.62  fof(f48,plain,(
% 1.48/0.62    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 1.48/0.62    inference(avatar_component_clause,[],[f46])).
% 1.48/0.62  fof(f63,plain,(
% 1.48/0.62    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 1.48/0.62    inference(superposition,[],[f26,f51])).
% 1.48/0.62  fof(f51,plain,(
% 1.48/0.62    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 1.48/0.62    inference(avatar_component_clause,[],[f50])).
% 1.48/0.62  fof(f54,plain,(
% 1.48/0.62    spl3_1 | spl3_2),
% 1.48/0.62    inference(avatar_split_clause,[],[f23,f50,f46])).
% 1.48/0.62  fof(f23,plain,(
% 1.48/0.62    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 1.48/0.62    inference(cnf_transformation,[],[f16])).
% 1.48/0.62  fof(f16,plain,(
% 1.48/0.62    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 1.48/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 1.48/0.62  fof(f15,plain,(
% 1.48/0.62    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 1.48/0.62    introduced(choice_axiom,[])).
% 1.48/0.62  fof(f14,plain,(
% 1.48/0.62    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 1.48/0.62    inference(nnf_transformation,[],[f12])).
% 1.48/0.62  fof(f12,plain,(
% 1.48/0.62    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 1.48/0.62    inference(ennf_transformation,[],[f10])).
% 1.48/0.62  fof(f10,negated_conjecture,(
% 1.48/0.62    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.48/0.62    inference(negated_conjecture,[],[f9])).
% 1.48/0.62  fof(f9,conjecture,(
% 1.48/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.48/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.48/0.62  fof(f53,plain,(
% 1.48/0.62    ~spl3_1 | ~spl3_2),
% 1.48/0.62    inference(avatar_split_clause,[],[f24,f50,f46])).
% 1.48/0.62  fof(f24,plain,(
% 1.48/0.62    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 1.48/0.62    inference(cnf_transformation,[],[f16])).
% 1.48/0.62  % SZS output end Proof for theBenchmark
% 1.48/0.62  % (29370)------------------------------
% 1.48/0.62  % (29370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.62  % (29370)Termination reason: Refutation
% 1.48/0.62  
% 1.48/0.62  % (29370)Memory used [KB]: 11129
% 1.48/0.62  % (29370)Time elapsed: 0.177 s
% 1.48/0.62  % (29370)------------------------------
% 1.48/0.62  % (29370)------------------------------
% 1.48/0.63  % (29343)Success in time 0.262 s
%------------------------------------------------------------------------------
