%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:09 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 146 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  246 ( 818 expanded)
%              Number of equality atoms :   96 ( 291 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1078,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f969,f1021,f1077])).

fof(f1077,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1076])).

fof(f1076,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1075,f53])).

fof(f53,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f1075,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1074,f73])).

fof(f73,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f36,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f1074,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1051,f35])).

fof(f35,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f1051,plain,
    ( r2_hidden(sK1,sK2)
    | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl5_7 ),
    inference(superposition,[],[f50,f968])).

fof(f968,plain,
    ( sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f966])).

fof(f966,plain,
    ( spl5_7
  <=> sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f1021,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1020])).

fof(f1020,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f1019,f55])).

fof(f55,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1019,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f1018,f73])).

fof(f1018,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f995,f34])).

fof(f34,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f995,plain,
    ( r2_hidden(sK0,sK2)
    | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_6 ),
    inference(superposition,[],[f50,f964])).

fof(f964,plain,
    ( sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl5_6
  <=> sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f969,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f955,f966,f962])).

fof(f955,plain,
    ( sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2)
    | sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f912,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f912,plain,(
    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f911,f903])).

fof(f903,plain,(
    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(duplicate_literal_removal,[],[f902])).

fof(f902,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)
    | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( sK2 != X0
      | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),sK2)
      | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f73,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f911,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(subsumption_resolution,[],[f904,f73])).

fof(f904,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(resolution,[],[f903,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26100)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (26108)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (26094)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (26116)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (26098)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (26096)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (26097)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (26095)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (26114)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (26112)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.54  % (26122)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.46/0.54  % (26094)Refutation not found, incomplete strategy% (26094)------------------------------
% 1.46/0.54  % (26094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (26113)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.54  % (26094)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  % (26110)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.54  
% 1.46/0.54  % (26094)Memory used [KB]: 1663
% 1.46/0.54  % (26094)Time elapsed: 0.138 s
% 1.46/0.54  % (26094)------------------------------
% 1.46/0.54  % (26094)------------------------------
% 1.46/0.55  % (26110)Refutation not found, incomplete strategy% (26110)------------------------------
% 1.46/0.55  % (26110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (26110)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (26110)Memory used [KB]: 1791
% 1.46/0.55  % (26110)Time elapsed: 0.144 s
% 1.46/0.55  % (26110)------------------------------
% 1.46/0.55  % (26110)------------------------------
% 1.46/0.55  % (26093)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.46/0.55  % (26103)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.46/0.55  % (26104)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.55  % (26120)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.55  % (26115)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.46/0.55  % (26119)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.55  % (26102)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.55  % (26106)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.55  % (26119)Refutation not found, incomplete strategy% (26119)------------------------------
% 1.46/0.55  % (26119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (26119)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (26119)Memory used [KB]: 6268
% 1.46/0.55  % (26119)Time elapsed: 0.153 s
% 1.46/0.55  % (26119)------------------------------
% 1.46/0.55  % (26119)------------------------------
% 1.46/0.55  % (26121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.56  % (26118)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.56  % (26122)Refutation not found, incomplete strategy% (26122)------------------------------
% 1.46/0.56  % (26122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (26122)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (26122)Memory used [KB]: 1663
% 1.46/0.56  % (26122)Time elapsed: 0.156 s
% 1.46/0.56  % (26122)------------------------------
% 1.46/0.56  % (26122)------------------------------
% 1.46/0.56  % (26107)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.59/0.56  % (26111)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.59/0.56  % (26107)Refutation not found, incomplete strategy% (26107)------------------------------
% 1.59/0.56  % (26107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (26107)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (26107)Memory used [KB]: 1663
% 1.59/0.56  % (26107)Time elapsed: 0.086 s
% 1.59/0.56  % (26107)------------------------------
% 1.59/0.56  % (26107)------------------------------
% 1.59/0.56  % (26105)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.59/0.56  % (26109)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.56  % (26099)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.57  % (26101)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.59/0.58  % (26117)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.58  % (26109)Refutation not found, incomplete strategy% (26109)------------------------------
% 1.59/0.58  % (26109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (26109)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (26109)Memory used [KB]: 10618
% 1.59/0.58  % (26109)Time elapsed: 0.178 s
% 1.59/0.58  % (26109)------------------------------
% 1.59/0.58  % (26109)------------------------------
% 2.28/0.67  % (26160)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.28/0.68  % (26157)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.28/0.68  % (26160)Refutation not found, incomplete strategy% (26160)------------------------------
% 2.28/0.68  % (26160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (26160)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.68  
% 2.28/0.68  % (26160)Memory used [KB]: 10746
% 2.28/0.68  % (26160)Time elapsed: 0.062 s
% 2.28/0.68  % (26160)------------------------------
% 2.28/0.68  % (26160)------------------------------
% 2.28/0.69  % (26096)Refutation not found, incomplete strategy% (26096)------------------------------
% 2.28/0.69  % (26096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.69  % (26096)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.69  
% 2.28/0.69  % (26096)Memory used [KB]: 6140
% 2.28/0.69  % (26096)Time elapsed: 0.283 s
% 2.28/0.69  % (26096)------------------------------
% 2.28/0.69  % (26096)------------------------------
% 2.28/0.69  % (26159)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.28/0.69  % (26158)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.28/0.69  % (26156)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.28/0.70  % (26105)Refutation found. Thanks to Tanya!
% 2.28/0.70  % SZS status Theorem for theBenchmark
% 2.28/0.72  % SZS output start Proof for theBenchmark
% 2.28/0.72  fof(f1078,plain,(
% 2.28/0.72    $false),
% 2.28/0.72    inference(avatar_sat_refutation,[],[f969,f1021,f1077])).
% 2.28/0.72  fof(f1077,plain,(
% 2.28/0.72    ~spl5_7),
% 2.28/0.72    inference(avatar_contradiction_clause,[],[f1076])).
% 2.28/0.72  fof(f1076,plain,(
% 2.28/0.72    $false | ~spl5_7),
% 2.28/0.72    inference(subsumption_resolution,[],[f1075,f53])).
% 2.28/0.72  fof(f53,plain,(
% 2.28/0.72    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 2.28/0.72    inference(equality_resolution,[],[f52])).
% 2.28/0.72  fof(f52,plain,(
% 2.28/0.72    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 2.28/0.72    inference(equality_resolution,[],[f42])).
% 2.28/0.72  fof(f42,plain,(
% 2.28/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.28/0.72    inference(cnf_transformation,[],[f28])).
% 2.28/0.72  fof(f28,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.28/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 2.28/0.72  fof(f27,plain,(
% 2.28/0.72    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.28/0.72    introduced(choice_axiom,[])).
% 2.28/0.72  fof(f26,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.28/0.72    inference(rectify,[],[f25])).
% 2.28/0.72  fof(f25,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.28/0.72    inference(flattening,[],[f24])).
% 2.28/0.72  fof(f24,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.28/0.72    inference(nnf_transformation,[],[f11])).
% 2.28/0.72  fof(f11,axiom,(
% 2.28/0.72    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.28/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.28/0.72  fof(f1075,plain,(
% 2.28/0.72    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~spl5_7),
% 2.28/0.72    inference(subsumption_resolution,[],[f1074,f73])).
% 2.28/0.72  fof(f73,plain,(
% 2.28/0.72    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.28/0.72    inference(superposition,[],[f36,f37])).
% 2.28/0.72  fof(f37,plain,(
% 2.28/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.28/0.72    inference(cnf_transformation,[],[f6])).
% 2.28/0.72  fof(f6,axiom,(
% 2.28/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.28/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.28/0.72  fof(f36,plain,(
% 2.28/0.72    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.28/0.72    inference(cnf_transformation,[],[f23])).
% 2.28/0.72  fof(f23,plain,(
% 2.28/0.72    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 2.28/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 2.28/0.72  fof(f22,plain,(
% 2.28/0.72    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 2.28/0.72    introduced(choice_axiom,[])).
% 2.28/0.72  fof(f21,plain,(
% 2.28/0.72    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.28/0.72    inference(ennf_transformation,[],[f19])).
% 2.28/0.72  fof(f19,negated_conjecture,(
% 2.28/0.72    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.28/0.72    inference(negated_conjecture,[],[f18])).
% 2.28/0.72  fof(f18,conjecture,(
% 2.28/0.72    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.28/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 2.28/0.72  fof(f1074,plain,(
% 2.28/0.72    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~spl5_7),
% 2.28/0.72    inference(subsumption_resolution,[],[f1051,f35])).
% 2.28/0.72  fof(f35,plain,(
% 2.28/0.72    ~r2_hidden(sK1,sK2)),
% 2.28/0.72    inference(cnf_transformation,[],[f23])).
% 2.28/0.72  fof(f1051,plain,(
% 2.28/0.72    r2_hidden(sK1,sK2) | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~spl5_7),
% 2.28/0.72    inference(superposition,[],[f50,f968])).
% 2.28/0.72  fof(f968,plain,(
% 2.28/0.72    sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2) | ~spl5_7),
% 2.28/0.72    inference(avatar_component_clause,[],[f966])).
% 2.28/0.72  fof(f966,plain,(
% 2.28/0.72    spl5_7 <=> sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2)),
% 2.28/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.28/0.72  fof(f50,plain,(
% 2.28/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.28/0.72    inference(cnf_transformation,[],[f33])).
% 2.28/0.72  fof(f33,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.28/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 2.28/0.72  fof(f32,plain,(
% 2.28/0.72    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 2.28/0.72    introduced(choice_axiom,[])).
% 2.28/0.72  fof(f31,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.28/0.72    inference(rectify,[],[f30])).
% 2.28/0.72  fof(f30,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.28/0.72    inference(flattening,[],[f29])).
% 2.28/0.72  fof(f29,plain,(
% 2.28/0.72    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.28/0.72    inference(nnf_transformation,[],[f2])).
% 2.28/0.72  fof(f2,axiom,(
% 2.28/0.72    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.28/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.28/0.72  fof(f1021,plain,(
% 2.28/0.72    ~spl5_6),
% 2.28/0.72    inference(avatar_contradiction_clause,[],[f1020])).
% 2.28/0.72  fof(f1020,plain,(
% 2.28/0.72    $false | ~spl5_6),
% 2.28/0.72    inference(subsumption_resolution,[],[f1019,f55])).
% 2.28/0.72  fof(f55,plain,(
% 2.28/0.72    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.28/0.72    inference(equality_resolution,[],[f54])).
% 2.28/0.72  fof(f54,plain,(
% 2.28/0.72    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.28/0.72    inference(equality_resolution,[],[f41])).
% 2.28/0.72  fof(f41,plain,(
% 2.28/0.72    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.28/0.72    inference(cnf_transformation,[],[f28])).
% 2.28/0.72  fof(f1019,plain,(
% 2.28/0.72    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_6),
% 2.28/0.72    inference(subsumption_resolution,[],[f1018,f73])).
% 2.28/0.72  fof(f1018,plain,(
% 2.28/0.72    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_6),
% 2.28/0.72    inference(subsumption_resolution,[],[f995,f34])).
% 2.28/0.72  fof(f34,plain,(
% 2.28/0.72    ~r2_hidden(sK0,sK2)),
% 2.28/0.72    inference(cnf_transformation,[],[f23])).
% 2.28/0.72  fof(f995,plain,(
% 2.28/0.72    r2_hidden(sK0,sK2) | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_6),
% 2.28/0.72    inference(superposition,[],[f50,f964])).
% 2.28/0.72  fof(f964,plain,(
% 2.28/0.72    sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2) | ~spl5_6),
% 2.28/0.72    inference(avatar_component_clause,[],[f962])).
% 2.28/0.72  fof(f962,plain,(
% 2.28/0.72    spl5_6 <=> sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2)),
% 2.28/0.72    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.28/0.72  fof(f969,plain,(
% 2.28/0.72    spl5_6 | spl5_7),
% 2.28/0.72    inference(avatar_split_clause,[],[f955,f966,f962])).
% 2.28/0.72  fof(f955,plain,(
% 2.28/0.72    sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2) | sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2)),
% 2.28/0.72    inference(resolution,[],[f912,f56])).
% 2.28/0.72  fof(f56,plain,(
% 2.28/0.72    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 2.28/0.72    inference(equality_resolution,[],[f40])).
% 2.28/0.72  fof(f40,plain,(
% 2.28/0.72    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 2.28/0.72    inference(cnf_transformation,[],[f28])).
% 2.28/0.72  fof(f912,plain,(
% 2.28/0.72    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))),
% 2.28/0.72    inference(subsumption_resolution,[],[f911,f903])).
% 2.28/0.72  fof(f903,plain,(
% 2.28/0.72    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 2.28/0.72    inference(duplicate_literal_removal,[],[f902])).
% 2.28/0.72  fof(f902,plain,(
% 2.28/0.72    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 2.28/0.72    inference(equality_resolution,[],[f91])).
% 2.28/0.72  fof(f91,plain,(
% 2.28/0.72    ( ! [X0] : (sK2 != X0 | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),sK2) | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),X0)) )),
% 2.28/0.72    inference(superposition,[],[f73,f49])).
% 2.28/0.72  fof(f49,plain,(
% 2.28/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.28/0.72    inference(cnf_transformation,[],[f33])).
% 2.28/0.72  fof(f911,plain,(
% 2.28/0.72    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 2.28/0.72    inference(subsumption_resolution,[],[f904,f73])).
% 2.28/0.72  fof(f904,plain,(
% 2.28/0.72    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 2.28/0.72    inference(resolution,[],[f903,f51])).
% 2.28/0.72  fof(f51,plain,(
% 2.28/0.72    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 2.28/0.72    inference(cnf_transformation,[],[f33])).
% 2.28/0.72  % SZS output end Proof for theBenchmark
% 2.28/0.72  % (26105)------------------------------
% 2.28/0.72  % (26105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.72  % (26105)Termination reason: Refutation
% 2.28/0.72  
% 2.28/0.72  % (26105)Memory used [KB]: 11641
% 2.28/0.72  % (26105)Time elapsed: 0.310 s
% 2.28/0.72  % (26105)------------------------------
% 2.28/0.72  % (26105)------------------------------
% 2.28/0.72  % (26092)Success in time 0.363 s
%------------------------------------------------------------------------------
