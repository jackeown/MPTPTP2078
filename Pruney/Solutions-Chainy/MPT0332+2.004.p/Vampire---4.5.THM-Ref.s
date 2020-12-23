%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:09 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.98s
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
fof(f1079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f970,f1022,f1078])).

fof(f1078,plain,(
    ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f1077])).

fof(f1077,plain,
    ( $false
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1076,f54])).

fof(f54,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f1076,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1075,f74])).

fof(f74,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f37,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f1075,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f1052,f36])).

fof(f36,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f1052,plain,
    ( r2_hidden(sK1,sK2)
    | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl5_7 ),
    inference(superposition,[],[f51,f969])).

fof(f969,plain,
    ( sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f967])).

fof(f967,plain,
    ( spl5_7
  <=> sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1022,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f1020,f56])).

fof(f56,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1020,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f1019,f74])).

fof(f1019,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f996,f35])).

fof(f35,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f996,plain,
    ( r2_hidden(sK0,sK2)
    | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl5_6 ),
    inference(superposition,[],[f51,f965])).

fof(f965,plain,
    ( sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f963])).

fof(f963,plain,
    ( spl5_6
  <=> sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f970,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f956,f967,f963])).

fof(f956,plain,
    ( sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2)
    | sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f913,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f913,plain,(
    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f912,f904])).

fof(f904,plain,(
    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(duplicate_literal_removal,[],[f903])).

fof(f903,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)
    | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( sK2 != X0
      | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),sK2)
      | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f74,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f912,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(subsumption_resolution,[],[f905,f74])).

fof(f905,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(resolution,[],[f904,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (12742)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (12757)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (12751)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (12740)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (12749)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (12734)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (12730)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (12733)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (12743)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (12736)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (12731)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.53  % (12731)Refutation not found, incomplete strategy% (12731)------------------------------
% 1.27/0.53  % (12731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (12731)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (12731)Memory used [KB]: 1663
% 1.27/0.53  % (12731)Time elapsed: 0.114 s
% 1.27/0.53  % (12731)------------------------------
% 1.27/0.53  % (12731)------------------------------
% 1.27/0.53  % (12759)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.53  % (12754)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.53  % (12738)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.53  % (12732)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.53  % (12757)Refutation not found, incomplete strategy% (12757)------------------------------
% 1.27/0.53  % (12757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (12757)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (12757)Memory used [KB]: 6268
% 1.27/0.53  % (12757)Time elapsed: 0.116 s
% 1.27/0.53  % (12757)------------------------------
% 1.27/0.53  % (12757)------------------------------
% 1.27/0.54  % (12735)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.54  % (12758)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.54  % (12737)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.54  % (12755)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.54  % (12748)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.55  % (12747)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.55  % (12739)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.55  % (12756)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.55  % (12747)Refutation not found, incomplete strategy% (12747)------------------------------
% 1.44/0.55  % (12747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (12747)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (12747)Memory used [KB]: 10618
% 1.44/0.55  % (12747)Time elapsed: 0.138 s
% 1.44/0.55  % (12747)------------------------------
% 1.44/0.55  % (12747)------------------------------
% 1.44/0.55  % (12748)Refutation not found, incomplete strategy% (12748)------------------------------
% 1.44/0.55  % (12748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (12748)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (12748)Memory used [KB]: 1791
% 1.44/0.55  % (12748)Time elapsed: 0.137 s
% 1.44/0.55  % (12748)------------------------------
% 1.44/0.55  % (12748)------------------------------
% 1.44/0.55  % (12750)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.55  % (12741)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.55  % (12760)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.55  % (12760)Refutation not found, incomplete strategy% (12760)------------------------------
% 1.44/0.55  % (12760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (12746)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.55  % (12760)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (12760)Memory used [KB]: 1663
% 1.44/0.55  % (12760)Time elapsed: 0.139 s
% 1.44/0.55  % (12760)------------------------------
% 1.44/0.55  % (12760)------------------------------
% 1.44/0.55  % (12753)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.44/0.55  % (12752)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.56  % (12745)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.44/0.56  % (12745)Refutation not found, incomplete strategy% (12745)------------------------------
% 1.44/0.56  % (12745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (12745)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (12745)Memory used [KB]: 1663
% 1.44/0.56  % (12745)Time elapsed: 0.146 s
% 1.44/0.56  % (12745)------------------------------
% 1.44/0.56  % (12745)------------------------------
% 1.44/0.62  % (12742)Refutation found. Thanks to Tanya!
% 1.44/0.62  % SZS status Theorem for theBenchmark
% 1.98/0.63  % SZS output start Proof for theBenchmark
% 1.98/0.63  fof(f1079,plain,(
% 1.98/0.63    $false),
% 1.98/0.63    inference(avatar_sat_refutation,[],[f970,f1022,f1078])).
% 1.98/0.63  fof(f1078,plain,(
% 1.98/0.63    ~spl5_7),
% 1.98/0.63    inference(avatar_contradiction_clause,[],[f1077])).
% 1.98/0.63  fof(f1077,plain,(
% 1.98/0.63    $false | ~spl5_7),
% 1.98/0.63    inference(subsumption_resolution,[],[f1076,f54])).
% 1.98/0.63  fof(f54,plain,(
% 1.98/0.63    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.98/0.63    inference(equality_resolution,[],[f53])).
% 1.98/0.63  fof(f53,plain,(
% 1.98/0.63    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.98/0.63    inference(equality_resolution,[],[f43])).
% 1.98/0.63  fof(f43,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.98/0.63    inference(cnf_transformation,[],[f29])).
% 1.98/0.63  fof(f29,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.98/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.98/0.63  fof(f28,plain,(
% 1.98/0.63    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.98/0.63    introduced(choice_axiom,[])).
% 1.98/0.63  fof(f27,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.98/0.63    inference(rectify,[],[f26])).
% 1.98/0.63  fof(f26,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.98/0.63    inference(flattening,[],[f25])).
% 1.98/0.63  fof(f25,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.98/0.63    inference(nnf_transformation,[],[f11])).
% 1.98/0.63  fof(f11,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.98/0.63  fof(f1076,plain,(
% 1.98/0.63    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~spl5_7),
% 1.98/0.63    inference(subsumption_resolution,[],[f1075,f74])).
% 1.98/0.63  fof(f74,plain,(
% 1.98/0.63    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 1.98/0.63    inference(superposition,[],[f37,f38])).
% 1.98/0.63  fof(f38,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f6])).
% 1.98/0.63  fof(f6,axiom,(
% 1.98/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.98/0.63  fof(f37,plain,(
% 1.98/0.63    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.98/0.63    inference(cnf_transformation,[],[f24])).
% 1.98/0.63  fof(f24,plain,(
% 1.98/0.63    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 1.98/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 1.98/0.63  fof(f23,plain,(
% 1.98/0.63    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 1.98/0.63    introduced(choice_axiom,[])).
% 1.98/0.63  fof(f22,plain,(
% 1.98/0.63    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.98/0.63    inference(ennf_transformation,[],[f20])).
% 1.98/0.63  fof(f20,negated_conjecture,(
% 1.98/0.63    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.98/0.63    inference(negated_conjecture,[],[f19])).
% 1.98/0.63  fof(f19,conjecture,(
% 1.98/0.63    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 1.98/0.63  fof(f1075,plain,(
% 1.98/0.63    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~spl5_7),
% 1.98/0.63    inference(subsumption_resolution,[],[f1052,f36])).
% 1.98/0.63  fof(f36,plain,(
% 1.98/0.63    ~r2_hidden(sK1,sK2)),
% 1.98/0.63    inference(cnf_transformation,[],[f24])).
% 1.98/0.63  fof(f1052,plain,(
% 1.98/0.63    r2_hidden(sK1,sK2) | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | ~spl5_7),
% 1.98/0.63    inference(superposition,[],[f51,f969])).
% 1.98/0.63  fof(f969,plain,(
% 1.98/0.63    sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2) | ~spl5_7),
% 1.98/0.63    inference(avatar_component_clause,[],[f967])).
% 1.98/0.63  fof(f967,plain,(
% 1.98/0.63    spl5_7 <=> sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2)),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.98/0.63  fof(f51,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f34])).
% 1.98/0.63  fof(f34,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.98/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.98/0.63  fof(f33,plain,(
% 1.98/0.63    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.98/0.63    introduced(choice_axiom,[])).
% 1.98/0.63  fof(f32,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.98/0.63    inference(rectify,[],[f31])).
% 1.98/0.63  fof(f31,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.98/0.63    inference(flattening,[],[f30])).
% 1.98/0.63  fof(f30,plain,(
% 1.98/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.98/0.63    inference(nnf_transformation,[],[f2])).
% 1.98/0.63  fof(f2,axiom,(
% 1.98/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.98/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.98/0.63  fof(f1022,plain,(
% 1.98/0.63    ~spl5_6),
% 1.98/0.63    inference(avatar_contradiction_clause,[],[f1021])).
% 1.98/0.63  fof(f1021,plain,(
% 1.98/0.63    $false | ~spl5_6),
% 1.98/0.63    inference(subsumption_resolution,[],[f1020,f56])).
% 1.98/0.63  fof(f56,plain,(
% 1.98/0.63    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.98/0.63    inference(equality_resolution,[],[f55])).
% 1.98/0.63  fof(f55,plain,(
% 1.98/0.63    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.98/0.63    inference(equality_resolution,[],[f42])).
% 1.98/0.63  fof(f42,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.98/0.63    inference(cnf_transformation,[],[f29])).
% 1.98/0.63  fof(f1020,plain,(
% 1.98/0.63    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_6),
% 1.98/0.63    inference(subsumption_resolution,[],[f1019,f74])).
% 1.98/0.63  fof(f1019,plain,(
% 1.98/0.63    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_6),
% 1.98/0.63    inference(subsumption_resolution,[],[f996,f35])).
% 1.98/0.63  fof(f35,plain,(
% 1.98/0.63    ~r2_hidden(sK0,sK2)),
% 1.98/0.63    inference(cnf_transformation,[],[f24])).
% 1.98/0.63  fof(f996,plain,(
% 1.98/0.63    r2_hidden(sK0,sK2) | sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | ~spl5_6),
% 1.98/0.63    inference(superposition,[],[f51,f965])).
% 1.98/0.63  fof(f965,plain,(
% 1.98/0.63    sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2) | ~spl5_6),
% 1.98/0.63    inference(avatar_component_clause,[],[f963])).
% 1.98/0.63  fof(f963,plain,(
% 1.98/0.63    spl5_6 <=> sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2)),
% 1.98/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.98/0.63  fof(f970,plain,(
% 1.98/0.63    spl5_6 | spl5_7),
% 1.98/0.63    inference(avatar_split_clause,[],[f956,f967,f963])).
% 1.98/0.63  fof(f956,plain,(
% 1.98/0.63    sK1 = sK4(sK2,k2_tarski(sK0,sK1),sK2) | sK0 = sK4(sK2,k2_tarski(sK0,sK1),sK2)),
% 1.98/0.63    inference(resolution,[],[f913,f57])).
% 1.98/0.63  fof(f57,plain,(
% 1.98/0.63    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 1.98/0.63    inference(equality_resolution,[],[f41])).
% 1.98/0.63  fof(f41,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.98/0.63    inference(cnf_transformation,[],[f29])).
% 1.98/0.63  fof(f913,plain,(
% 1.98/0.63    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))),
% 1.98/0.63    inference(subsumption_resolution,[],[f912,f904])).
% 1.98/0.63  fof(f904,plain,(
% 1.98/0.63    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 1.98/0.63    inference(duplicate_literal_removal,[],[f903])).
% 1.98/0.63  fof(f903,plain,(
% 1.98/0.63    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2) | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 1.98/0.63    inference(equality_resolution,[],[f92])).
% 1.98/0.63  fof(f92,plain,(
% 1.98/0.63    ( ! [X0] : (sK2 != X0 | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),sK2) | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),X0),X0)) )),
% 1.98/0.63    inference(superposition,[],[f74,f50])).
% 1.98/0.63  fof(f50,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f34])).
% 1.98/0.63  fof(f912,plain,(
% 1.98/0.63    r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 1.98/0.63    inference(subsumption_resolution,[],[f905,f74])).
% 1.98/0.63  fof(f905,plain,(
% 1.98/0.63    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | ~r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),sK2),sK2)),
% 1.98/0.63    inference(resolution,[],[f904,f52])).
% 1.98/0.63  fof(f52,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f34])).
% 1.98/0.63  % SZS output end Proof for theBenchmark
% 1.98/0.63  % (12742)------------------------------
% 1.98/0.63  % (12742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.63  % (12742)Termination reason: Refutation
% 1.98/0.63  
% 1.98/0.63  % (12742)Memory used [KB]: 11641
% 1.98/0.63  % (12742)Time elapsed: 0.198 s
% 1.98/0.63  % (12742)------------------------------
% 1.98/0.63  % (12742)------------------------------
% 1.98/0.63  % (12726)Success in time 0.27 s
%------------------------------------------------------------------------------
