%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 162 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 578 expanded)
%              Number of equality atoms :   16 (  50 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f155,f188])).

fof(f188,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f186,f93])).

% (28879)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f93,plain,(
    r2_hidden(sK6(sK0),sK1) ),
    inference(resolution,[],[f73,f20])).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
    & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
        & r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
      & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
      & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK6(sK0),X0) ) ),
    inference(resolution,[],[f39,f20])).

fof(f39,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X5,k2_zfmisc_1(X8,X9))
      | r2_hidden(sK6(X5),X6)
      | ~ r2_hidden(X5,k2_zfmisc_1(X6,X7)) ) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK6(X0),sK7(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f8,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK6(X0),sK7(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f186,plain,
    ( ~ r2_hidden(sK6(sK0),sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f185,f94])).

fof(f94,plain,(
    r2_hidden(sK6(sK0),sK3) ),
    inference(resolution,[],[f73,f21])).

fof(f21,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f185,plain,
    ( ~ r2_hidden(sK6(sK0),sK3)
    | ~ r2_hidden(sK6(sK0),sK1)
    | spl8_2 ),
    inference(resolution,[],[f133,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f133,plain,
    ( ~ r2_hidden(sK6(sK0),k3_xboole_0(sK1,sK3))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_2
  <=> r2_hidden(sK6(sK0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f155,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f153,f54])).

fof(f54,plain,(
    r2_hidden(sK7(sK0),sK2) ),
    inference(resolution,[],[f43,f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X1,X0))
      | r2_hidden(sK7(sK0),X0) ) ),
    inference(resolution,[],[f38,f20])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | r2_hidden(sK7(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(superposition,[],[f31,f29])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f153,plain,
    ( ~ r2_hidden(sK7(sK0),sK2)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f152,f55])).

fof(f55,plain,(
    r2_hidden(sK7(sK0),sK4) ),
    inference(resolution,[],[f43,f21])).

fof(f152,plain,
    ( ~ r2_hidden(sK7(sK0),sK4)
    | ~ r2_hidden(sK7(sK0),sK2)
    | spl8_1 ),
    inference(resolution,[],[f130,f33])).

fof(f130,plain,
    ( ~ r2_hidden(sK7(sK0),k3_xboole_0(sK2,sK4))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_1
  <=> r2_hidden(sK7(sK0),k3_xboole_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f134,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f122,f132,f129])).

fof(f122,plain,
    ( ~ r2_hidden(sK6(sK0),k3_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK7(sK0),k3_xboole_0(sK2,sK4)) ),
    inference(resolution,[],[f80,f22])).

fof(f22,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,k2_zfmisc_1(X1,X0))
      | ~ r2_hidden(sK6(sK0),X1)
      | ~ r2_hidden(sK7(sK0),X0) ) ),
    inference(resolution,[],[f42,f20])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(sK7(X0),X2)
      | ~ r2_hidden(sK6(X0),X1)
      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(superposition,[],[f32,f29])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (28870)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.42  % (28880)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (28866)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (28877)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (28865)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (28869)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (28875)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (28863)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (28867)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (28872)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (28864)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (28864)Refutation not found, incomplete strategy% (28864)------------------------------
% 0.20/0.50  % (28864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28864)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28864)Memory used [KB]: 10490
% 0.20/0.50  % (28864)Time elapsed: 0.093 s
% 0.20/0.50  % (28864)------------------------------
% 0.20/0.50  % (28864)------------------------------
% 0.20/0.50  % (28868)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (28881)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (28878)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (28883)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (28883)Refutation not found, incomplete strategy% (28883)------------------------------
% 0.20/0.51  % (28883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28883)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28883)Memory used [KB]: 10490
% 0.20/0.51  % (28883)Time elapsed: 0.105 s
% 0.20/0.51  % (28883)------------------------------
% 0.20/0.51  % (28883)------------------------------
% 0.20/0.51  % (28876)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (28865)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f134,f155,f188])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    spl8_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    $false | spl8_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f186,f93])).
% 0.20/0.51  % (28879)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    r2_hidden(sK6(sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f73,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => (~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) & r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) & r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(flattening,[],[f6])).
% 0.20/0.51  fof(f6,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & (r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.20/0.51    inference(negated_conjecture,[],[f4])).
% 0.20/0.51  fof(f4,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK6(sK0),X0)) )),
% 0.20/0.51    inference(resolution,[],[f39,f20])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X6,X8,X7,X5,X9] : (~r2_hidden(X5,k2_zfmisc_1(X8,X9)) | r2_hidden(sK6(X5),X6) | ~r2_hidden(X5,k2_zfmisc_1(X6,X7))) )),
% 0.20/0.51    inference(superposition,[],[f30,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_tarski(sK6(X0),sK7(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f8,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK6(X0),sK7(X0)) = X0)),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.51    inference(flattening,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ~r2_hidden(sK6(sK0),sK1) | spl8_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f185,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    r2_hidden(sK6(sK0),sK3)),
% 0.20/0.51    inference(resolution,[],[f73,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f185,plain,(
% 0.20/0.51    ~r2_hidden(sK6(sK0),sK3) | ~r2_hidden(sK6(sK0),sK1) | spl8_2),
% 0.20/0.51    inference(resolution,[],[f133,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.51    inference(rectify,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ~r2_hidden(sK6(sK0),k3_xboole_0(sK1,sK3)) | spl8_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    spl8_2 <=> r2_hidden(sK6(sK0),k3_xboole_0(sK1,sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    spl8_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    $false | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f153,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    r2_hidden(sK7(sK0),sK2)),
% 0.20/0.51    inference(resolution,[],[f43,f20])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X1,X0)) | r2_hidden(sK7(sK0),X0)) )),
% 0.20/0.51    inference(resolution,[],[f38,f20])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | r2_hidden(sK7(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(superposition,[],[f31,f29])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ~r2_hidden(sK7(sK0),sK2) | spl8_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f152,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    r2_hidden(sK7(sK0),sK4)),
% 0.20/0.51    inference(resolution,[],[f43,f21])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ~r2_hidden(sK7(sK0),sK4) | ~r2_hidden(sK7(sK0),sK2) | spl8_1),
% 0.20/0.51    inference(resolution,[],[f130,f33])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ~r2_hidden(sK7(sK0),k3_xboole_0(sK2,sK4)) | spl8_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f129])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    spl8_1 <=> r2_hidden(sK7(sK0),k3_xboole_0(sK2,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ~spl8_1 | ~spl8_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f122,f132,f129])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ~r2_hidden(sK6(sK0),k3_xboole_0(sK1,sK3)) | ~r2_hidden(sK7(sK0),k3_xboole_0(sK2,sK4))),
% 0.20/0.51    inference(resolution,[],[f80,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X1,X0)) | ~r2_hidden(sK6(sK0),X1) | ~r2_hidden(sK7(sK0),X0)) )),
% 0.20/0.51    inference(resolution,[],[f42,f20])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | ~r2_hidden(sK7(X0),X2) | ~r2_hidden(sK6(X0),X1) | r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.51    inference(superposition,[],[f32,f29])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28865)------------------------------
% 0.20/0.51  % (28865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28865)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (28865)Memory used [KB]: 10746
% 0.20/0.51  % (28865)Time elapsed: 0.105 s
% 0.20/0.51  % (28865)------------------------------
% 0.20/0.51  % (28865)------------------------------
% 0.20/0.51  % (28874)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (28862)Success in time 0.157 s
%------------------------------------------------------------------------------
