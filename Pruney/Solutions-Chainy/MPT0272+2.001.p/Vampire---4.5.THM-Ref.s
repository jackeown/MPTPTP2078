%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:11 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   59 (  86 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 315 expanded)
%              Number of equality atoms :   86 ( 131 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f116,f132,f174,f179,f289,f296,f303])).

fof(f303,plain,
    ( ~ spl5_10
    | ~ spl5_14
    | spl5_35
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_14
    | spl5_35
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f290,f297])).

fof(f297,plain,
    ( r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k1_tarski(sK0))
    | ~ spl5_14
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f295,f131])).

fof(f131,plain,
    ( ! [X4,X0,X1] :
        ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
        | r2_hidden(X4,X0) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_14
  <=> ! [X1,X0,X4] :
        ( r2_hidden(X4,X0)
        | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f295,plain,
    ( r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl5_36
  <=> r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k4_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f290,plain,
    ( ~ r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k1_tarski(sK0))
    | ~ spl5_10
    | spl5_35 ),
    inference(unit_resulting_resolution,[],[f288,f115])).

fof(f115,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_tarski(X0))
        | X0 = X3 )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_10
  <=> ! [X3,X0] :
        ( X0 = X3
        | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f288,plain,
    ( sK0 != sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl5_35
  <=> sK0 = sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f296,plain,
    ( spl5_36
    | spl5_1
    | spl5_2
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f218,f172,f81,f76,f293])).

fof(f76,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,
    ( spl5_2
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f172,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),X0)
        | k1_xboole_0 = X0
        | k1_tarski(X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f218,plain,
    ( r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k4_xboole_0(k1_tarski(sK0),sK1))
    | spl5_1
    | spl5_2
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f83,f78,f173])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | k1_xboole_0 = X0
        | k1_tarski(X1) = X0 )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f172])).

fof(f78,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f83,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f289,plain,
    ( ~ spl5_35
    | spl5_1
    | spl5_2
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f222,f177,f81,f76,f286])).

fof(f177,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( sK3(X0,X1) != X1
        | k1_xboole_0 = X0
        | k1_tarski(X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f222,plain,
    ( sK0 != sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0)
    | spl5_1
    | spl5_2
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f83,f78,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( sK3(X0,X1) != X1
        | k1_xboole_0 = X0
        | k1_tarski(X1) = X0 )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f55,f177])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f174,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f54,f172])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f132,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f73,f130])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

% (32430)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f116,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f70,f114])).

fof(f70,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f84,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f79,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:21:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (32381)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % (32374)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (32373)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (32375)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (32365)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (32378)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (32371)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (32387)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (32381)Refutation not found, incomplete strategy% (32381)------------------------------
% 0.22/0.53  % (32381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32381)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32381)Memory used [KB]: 10618
% 0.22/0.53  % (32381)Time elapsed: 0.107 s
% 0.22/0.53  % (32381)------------------------------
% 0.22/0.53  % (32381)------------------------------
% 0.22/0.53  % (32386)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (32384)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (32390)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  % (32383)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (32383)Refutation not found, incomplete strategy% (32383)------------------------------
% 0.22/0.53  % (32383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32383)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32383)Memory used [KB]: 1663
% 0.22/0.53  % (32383)Time elapsed: 0.116 s
% 0.22/0.53  % (32383)------------------------------
% 0.22/0.53  % (32383)------------------------------
% 0.22/0.53  % (32370)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (32366)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (32366)Refutation not found, incomplete strategy% (32366)------------------------------
% 0.22/0.54  % (32366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32366)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32366)Memory used [KB]: 1663
% 0.22/0.54  % (32366)Time elapsed: 0.116 s
% 0.22/0.54  % (32366)------------------------------
% 0.22/0.54  % (32366)------------------------------
% 0.22/0.54  % (32382)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (32389)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (32369)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (32388)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (32376)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (32367)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (32368)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32393)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (32380)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (32392)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (32377)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (32379)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (32391)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (32392)Refutation not found, incomplete strategy% (32392)------------------------------
% 0.22/0.55  % (32392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32392)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32392)Memory used [KB]: 6140
% 0.22/0.55  % (32392)Time elapsed: 0.130 s
% 0.22/0.55  % (32392)------------------------------
% 0.22/0.55  % (32392)------------------------------
% 0.22/0.55  % (32391)Refutation not found, incomplete strategy% (32391)------------------------------
% 0.22/0.55  % (32391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32394)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (32379)Refutation not found, incomplete strategy% (32379)------------------------------
% 0.22/0.55  % (32379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32394)Refutation not found, incomplete strategy% (32394)------------------------------
% 0.22/0.55  % (32394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32372)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (32394)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32394)Memory used [KB]: 1663
% 0.22/0.55  % (32394)Time elapsed: 0.144 s
% 0.22/0.55  % (32394)------------------------------
% 0.22/0.55  % (32394)------------------------------
% 0.22/0.55  % (32379)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32379)Memory used [KB]: 1663
% 0.22/0.55  % (32379)Time elapsed: 0.138 s
% 0.22/0.55  % (32379)------------------------------
% 0.22/0.55  % (32379)------------------------------
% 0.22/0.55  % (32385)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (32391)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (32391)Memory used [KB]: 6140
% 0.22/0.56  % (32391)Time elapsed: 0.128 s
% 0.22/0.56  % (32391)------------------------------
% 0.22/0.56  % (32391)------------------------------
% 1.43/0.56  % (32389)Refutation not found, incomplete strategy% (32389)------------------------------
% 1.43/0.56  % (32389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (32389)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (32389)Memory used [KB]: 10618
% 1.43/0.56  % (32389)Time elapsed: 0.131 s
% 1.43/0.56  % (32389)------------------------------
% 1.43/0.56  % (32389)------------------------------
% 1.91/0.65  % (32416)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.05/0.66  % (32416)Refutation found. Thanks to Tanya!
% 2.05/0.66  % SZS status Theorem for theBenchmark
% 2.05/0.66  % SZS output start Proof for theBenchmark
% 2.05/0.66  fof(f304,plain,(
% 2.05/0.66    $false),
% 2.05/0.66    inference(avatar_sat_refutation,[],[f79,f84,f116,f132,f174,f179,f289,f296,f303])).
% 2.05/0.66  fof(f303,plain,(
% 2.05/0.66    ~spl5_10 | ~spl5_14 | spl5_35 | ~spl5_36),
% 2.05/0.66    inference(avatar_contradiction_clause,[],[f302])).
% 2.05/0.66  fof(f302,plain,(
% 2.05/0.66    $false | (~spl5_10 | ~spl5_14 | spl5_35 | ~spl5_36)),
% 2.05/0.66    inference(subsumption_resolution,[],[f290,f297])).
% 2.05/0.66  fof(f297,plain,(
% 2.05/0.66    r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k1_tarski(sK0)) | (~spl5_14 | ~spl5_36)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f295,f131])).
% 2.05/0.66  fof(f131,plain,(
% 2.05/0.66    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) ) | ~spl5_14),
% 2.05/0.66    inference(avatar_component_clause,[],[f130])).
% 2.05/0.66  fof(f130,plain,(
% 2.05/0.66    spl5_14 <=> ! [X1,X0,X4] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1)))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.05/0.66  fof(f295,plain,(
% 2.05/0.66    r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k4_xboole_0(k1_tarski(sK0),sK1)) | ~spl5_36),
% 2.05/0.66    inference(avatar_component_clause,[],[f293])).
% 2.05/0.66  fof(f293,plain,(
% 2.05/0.66    spl5_36 <=> r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k4_xboole_0(k1_tarski(sK0),sK1))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.05/0.66  fof(f290,plain,(
% 2.05/0.66    ~r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k1_tarski(sK0)) | (~spl5_10 | spl5_35)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f288,f115])).
% 2.05/0.66  fof(f115,plain,(
% 2.05/0.66    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) ) | ~spl5_10),
% 2.05/0.66    inference(avatar_component_clause,[],[f114])).
% 2.05/0.66  fof(f114,plain,(
% 2.05/0.66    spl5_10 <=> ! [X3,X0] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0)))),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.05/0.66  fof(f288,plain,(
% 2.05/0.66    sK0 != sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0) | spl5_35),
% 2.05/0.66    inference(avatar_component_clause,[],[f286])).
% 2.05/0.66  fof(f286,plain,(
% 2.05/0.66    spl5_35 <=> sK0 = sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.05/0.66  fof(f296,plain,(
% 2.05/0.66    spl5_36 | spl5_1 | spl5_2 | ~spl5_21),
% 2.05/0.66    inference(avatar_split_clause,[],[f218,f172,f81,f76,f293])).
% 2.05/0.66  fof(f76,plain,(
% 2.05/0.66    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.05/0.66  fof(f81,plain,(
% 2.05/0.66    spl5_2 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.05/0.66  fof(f172,plain,(
% 2.05/0.66    spl5_21 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.05/0.66  fof(f218,plain,(
% 2.05/0.66    r2_hidden(sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0),k4_xboole_0(k1_tarski(sK0),sK1)) | (spl5_1 | spl5_2 | ~spl5_21)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f83,f78,f173])).
% 2.05/0.66  fof(f173,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) ) | ~spl5_21),
% 2.05/0.66    inference(avatar_component_clause,[],[f172])).
% 2.05/0.66  fof(f78,plain,(
% 2.05/0.66    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl5_1),
% 2.05/0.66    inference(avatar_component_clause,[],[f76])).
% 2.05/0.66  fof(f83,plain,(
% 2.05/0.66    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl5_2),
% 2.05/0.66    inference(avatar_component_clause,[],[f81])).
% 2.05/0.66  fof(f289,plain,(
% 2.05/0.66    ~spl5_35 | spl5_1 | spl5_2 | ~spl5_22),
% 2.05/0.66    inference(avatar_split_clause,[],[f222,f177,f81,f76,f286])).
% 2.05/0.66  fof(f177,plain,(
% 2.05/0.66    spl5_22 <=> ! [X1,X0] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.05/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.05/0.66  fof(f222,plain,(
% 2.05/0.66    sK0 != sK3(k4_xboole_0(k1_tarski(sK0),sK1),sK0) | (spl5_1 | spl5_2 | ~spl5_22)),
% 2.05/0.66    inference(unit_resulting_resolution,[],[f83,f78,f178])).
% 2.05/0.66  fof(f178,plain,(
% 2.05/0.66    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) ) | ~spl5_22),
% 2.05/0.66    inference(avatar_component_clause,[],[f177])).
% 2.05/0.66  fof(f179,plain,(
% 2.05/0.66    spl5_22),
% 2.05/0.66    inference(avatar_split_clause,[],[f55,f177])).
% 2.05/0.66  fof(f55,plain,(
% 2.05/0.66    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f32])).
% 2.05/0.66  fof(f32,plain,(
% 2.05/0.66    ! [X0,X1] : ((sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).
% 2.05/0.66  fof(f31,plain,(
% 2.05/0.66    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f24,plain,(
% 2.05/0.66    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.05/0.66    inference(ennf_transformation,[],[f19])).
% 2.05/0.66  fof(f19,axiom,(
% 2.05/0.66    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 2.05/0.66  fof(f174,plain,(
% 2.05/0.66    spl5_21),
% 2.05/0.66    inference(avatar_split_clause,[],[f54,f172])).
% 2.05/0.66  fof(f54,plain,(
% 2.05/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 2.05/0.66    inference(cnf_transformation,[],[f32])).
% 2.05/0.66  fof(f132,plain,(
% 2.05/0.66    spl5_14),
% 2.05/0.66    inference(avatar_split_clause,[],[f73,f130])).
% 2.05/0.66  fof(f73,plain,(
% 2.05/0.66    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.05/0.66    inference(equality_resolution,[],[f58])).
% 2.05/0.66  fof(f58,plain,(
% 2.05/0.66    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.05/0.66    inference(cnf_transformation,[],[f37])).
% 2.05/0.66  fof(f37,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 2.05/0.66  fof(f36,plain,(
% 2.05/0.66    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f35,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(rectify,[],[f34])).
% 2.05/0.66  % (32430)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.05/0.66  fof(f34,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(flattening,[],[f33])).
% 2.05/0.66  fof(f33,plain,(
% 2.05/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.05/0.66    inference(nnf_transformation,[],[f2])).
% 2.05/0.66  fof(f2,axiom,(
% 2.05/0.66    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.05/0.66  fof(f116,plain,(
% 2.05/0.66    spl5_10),
% 2.05/0.66    inference(avatar_split_clause,[],[f70,f114])).
% 2.05/0.66  fof(f70,plain,(
% 2.05/0.66    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.05/0.66    inference(equality_resolution,[],[f50])).
% 2.05/0.66  fof(f50,plain,(
% 2.05/0.66    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.05/0.66    inference(cnf_transformation,[],[f30])).
% 2.05/0.66  fof(f30,plain,(
% 2.05/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 2.05/0.66  fof(f29,plain,(
% 2.05/0.66    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f28,plain,(
% 2.05/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.05/0.66    inference(rectify,[],[f27])).
% 2.05/0.66  fof(f27,plain,(
% 2.05/0.66    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.05/0.66    inference(nnf_transformation,[],[f9])).
% 2.05/0.66  fof(f9,axiom,(
% 2.05/0.66    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.05/0.66  fof(f84,plain,(
% 2.05/0.66    ~spl5_2),
% 2.05/0.66    inference(avatar_split_clause,[],[f39,f81])).
% 2.05/0.66  fof(f39,plain,(
% 2.05/0.66    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.05/0.66    inference(cnf_transformation,[],[f26])).
% 2.05/0.66  fof(f26,plain,(
% 2.05/0.66    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.05/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).
% 2.05/0.66  fof(f25,plain,(
% 2.05/0.66    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 2.05/0.66    introduced(choice_axiom,[])).
% 2.05/0.66  fof(f23,plain,(
% 2.05/0.66    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 2.05/0.66    inference(ennf_transformation,[],[f21])).
% 2.05/0.66  fof(f21,negated_conjecture,(
% 2.05/0.66    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 2.05/0.66    inference(negated_conjecture,[],[f20])).
% 2.05/0.66  fof(f20,conjecture,(
% 2.05/0.66    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 2.05/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 2.05/0.66  fof(f79,plain,(
% 2.05/0.66    ~spl5_1),
% 2.05/0.66    inference(avatar_split_clause,[],[f38,f76])).
% 2.05/0.66  fof(f38,plain,(
% 2.05/0.66    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.05/0.66    inference(cnf_transformation,[],[f26])).
% 2.05/0.66  % SZS output end Proof for theBenchmark
% 2.05/0.66  % (32416)------------------------------
% 2.05/0.66  % (32416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.66  % (32416)Termination reason: Refutation
% 2.05/0.66  
% 2.05/0.66  % (32416)Memory used [KB]: 6396
% 2.05/0.66  % (32416)Time elapsed: 0.074 s
% 2.05/0.66  % (32416)------------------------------
% 2.05/0.66  % (32416)------------------------------
% 2.05/0.66  % (32364)Success in time 0.284 s
%------------------------------------------------------------------------------
