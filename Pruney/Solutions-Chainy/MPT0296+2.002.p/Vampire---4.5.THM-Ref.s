%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:51 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 176 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  145 ( 452 expanded)
%              Number of equality atoms :   30 ( 121 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f313,f329,f338])).

fof(f338,plain,(
    spl13_2 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl13_2 ),
    inference(subsumption_resolution,[],[f336,f315])).

fof(f315,plain,(
    r2_hidden(sK9(sK3,sK4,sK0),sK1) ),
    inference(subsumption_resolution,[],[f301,f43])).

fof(f43,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f301,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK9(sK3,sK4,sK0),sK1) ),
    inference(superposition,[],[f74,f286])).

fof(f286,plain,(
    sK0 = k4_tarski(sK9(sK3,sK4,sK0),sK10(sK3,sK4,sK0)) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f48,f12])).

fof(f12,plain,(
    r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6] :
          ( ~ r2_hidden(X6,k3_xboole_0(X2,X4))
          | ~ r2_hidden(X5,k3_xboole_0(X1,X3))
          | k4_tarski(X5,X6) != X0 )
      & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6] :
              ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X5,k3_xboole_0(X1,X3))
                & k4_tarski(X5,X6) = X0 )
          & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6] :
            ~ ( r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X5,k3_xboole_0(X1,X3))
              & k4_tarski(X5,X6) = X0 )
        & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f74,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k1_tarski(sK0))
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f38,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f45,f64])).

fof(f64,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f13,f58])).

fof(f58,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f49,f12])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f336,plain,
    ( ~ r2_hidden(sK9(sK3,sK4,sK0),sK1)
    | spl13_2 ),
    inference(subsumption_resolution,[],[f335,f314])).

fof(f314,plain,(
    r2_hidden(sK9(sK3,sK4,sK0),sK3) ),
    inference(subsumption_resolution,[],[f300,f43])).

fof(f300,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK9(sK3,sK4,sK0),sK3) ),
    inference(superposition,[],[f73,f286])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k1_tarski(sK0))
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f38,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK3,sK4))
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f45,f63])).

fof(f63,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f13,f57])).

fof(f335,plain,
    ( ~ r2_hidden(sK9(sK3,sK4,sK0),sK3)
    | ~ r2_hidden(sK9(sK3,sK4,sK0),sK1)
    | spl13_2 ),
    inference(resolution,[],[f312,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f312,plain,
    ( ~ r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3))
    | spl13_2 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl13_2
  <=> r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f329,plain,(
    spl13_1 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl13_1 ),
    inference(subsumption_resolution,[],[f327,f316])).

fof(f316,plain,(
    r2_hidden(sK10(sK3,sK4,sK0),sK2) ),
    inference(subsumption_resolution,[],[f303,f43])).

fof(f303,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK10(sK3,sK4,sK0),sK2) ),
    inference(superposition,[],[f76,f286])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),k1_tarski(sK0))
      | r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f39,f70])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f327,plain,
    ( ~ r2_hidden(sK10(sK3,sK4,sK0),sK2)
    | spl13_1 ),
    inference(subsumption_resolution,[],[f326,f226])).

fof(f226,plain,(
    r2_hidden(sK10(sK3,sK4,sK0),sK4) ),
    inference(resolution,[],[f220,f43])).

fof(f220,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_tarski(sK10(sK3,sK4,sK0)))
      | r2_hidden(X1,sK4) ) ),
    inference(superposition,[],[f45,f213])).

fof(f213,plain,(
    sK4 = k2_xboole_0(k1_tarski(sK10(sK3,sK4,sK0)),sK4) ),
    inference(resolution,[],[f86,f57])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k2_xboole_0(k1_tarski(sK10(X1,X2,X0)),X2) = X2 ) ),
    inference(resolution,[],[f53,f13])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f326,plain,
    ( ~ r2_hidden(sK10(sK3,sK4,sK0),sK4)
    | ~ r2_hidden(sK10(sK3,sK4,sK0),sK2)
    | spl13_1 ),
    inference(resolution,[],[f308,f47])).

fof(f308,plain,
    ( ~ r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl13_1
  <=> r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f313,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f304,f310,f306])).

fof(f304,plain,
    ( ~ r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4)) ),
    inference(trivial_inequality_removal,[],[f296])).

fof(f296,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3))
    | ~ r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4)) ),
    inference(superposition,[],[f11,f286])).

fof(f11,plain,(
    ! [X6,X5] :
      ( k4_tarski(X5,X6) != sK0
      | ~ r2_hidden(X5,k3_xboole_0(sK1,sK3))
      | ~ r2_hidden(X6,k3_xboole_0(sK2,sK4)) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (19986)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.48  % (19995)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (19980)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (19998)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (19981)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (19987)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (19999)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (19991)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (19989)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (19996)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (19990)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (19977)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (19997)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (19979)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (19985)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (19988)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.44/0.55  % (19992)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.44/0.55  % (19999)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f339,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f313,f329,f338])).
% 1.44/0.55  fof(f338,plain,(
% 1.44/0.55    spl13_2),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f337])).
% 1.44/0.55  fof(f337,plain,(
% 1.44/0.55    $false | spl13_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f336,f315])).
% 1.44/0.55  fof(f315,plain,(
% 1.44/0.55    r2_hidden(sK9(sK3,sK4,sK0),sK1)),
% 1.44/0.55    inference(subsumption_resolution,[],[f301,f43])).
% 1.44/0.55  fof(f43,plain,(
% 1.44/0.55    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.44/0.55    inference(equality_resolution,[],[f42])).
% 1.44/0.55  fof(f42,plain,(
% 1.44/0.55    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.44/0.55    inference(equality_resolution,[],[f14])).
% 1.44/0.55  fof(f14,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f3])).
% 1.44/0.55  fof(f3,axiom,(
% 1.44/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.44/0.55  fof(f301,plain,(
% 1.44/0.55    ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK9(sK3,sK4,sK0),sK1)),
% 1.44/0.55    inference(superposition,[],[f74,f286])).
% 1.44/0.55  fof(f286,plain,(
% 1.44/0.55    sK0 = k4_tarski(sK9(sK3,sK4,sK0),sK10(sK3,sK4,sK0))),
% 1.44/0.55    inference(resolution,[],[f52,f57])).
% 1.44/0.55  fof(f57,plain,(
% 1.44/0.55    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 1.44/0.55    inference(resolution,[],[f48,f12])).
% 1.44/0.55  fof(f12,plain,(
% 1.44/0.55    r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 1.44/0.55    inference(cnf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,plain,(
% 1.44/0.55    ? [X0,X1,X2,X3,X4] : (! [X5,X6] : (~r2_hidden(X6,k3_xboole_0(X2,X4)) | ~r2_hidden(X5,k3_xboole_0(X1,X3)) | k4_tarski(X5,X6) != X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 1.44/0.55    inference(ennf_transformation,[],[f8])).
% 1.44/0.55  fof(f8,negated_conjecture,(
% 1.44/0.55    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 1.44/0.55    inference(negated_conjecture,[],[f7])).
% 1.44/0.55  fof(f7,conjecture,(
% 1.44/0.55    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6] : ~(r2_hidden(X6,k3_xboole_0(X2,X4)) & r2_hidden(X5,k3_xboole_0(X1,X3)) & k4_tarski(X5,X6) = X0) & r2_hidden(X0,k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).
% 1.44/0.55  fof(f48,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 1.44/0.55    inference(equality_resolution,[],[f28])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f2,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.44/0.55  fof(f52,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3) )),
% 1.44/0.55    inference(equality_resolution,[],[f36])).
% 1.44/0.55  fof(f36,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.44/0.55  fof(f74,plain,(
% 1.44/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k1_tarski(sK0)) | r2_hidden(X2,sK1)) )),
% 1.44/0.55    inference(resolution,[],[f38,f70])).
% 1.44/0.55  fof(f70,plain,(
% 1.44/0.55    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 1.44/0.55    inference(superposition,[],[f45,f64])).
% 1.44/0.55  fof(f64,plain,(
% 1.44/0.55    k2_zfmisc_1(sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK1,sK2))),
% 1.44/0.55    inference(resolution,[],[f13,f58])).
% 1.44/0.55  fof(f58,plain,(
% 1.44/0.55    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 1.44/0.55    inference(resolution,[],[f49,f12])).
% 1.44/0.55  fof(f49,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f27])).
% 1.44/0.55  fof(f27,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f13,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f10])).
% 1.44/0.55  fof(f10,plain,(
% 1.44/0.55    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.44/0.55    inference(ennf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.44/0.55  fof(f45,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f22])).
% 1.44/0.55  fof(f22,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.44/0.55  fof(f38,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f5])).
% 1.44/0.55  fof(f5,axiom,(
% 1.44/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.44/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.44/0.55  fof(f336,plain,(
% 1.44/0.55    ~r2_hidden(sK9(sK3,sK4,sK0),sK1) | spl13_2),
% 1.44/0.55    inference(subsumption_resolution,[],[f335,f314])).
% 1.44/0.55  fof(f314,plain,(
% 1.44/0.55    r2_hidden(sK9(sK3,sK4,sK0),sK3)),
% 1.44/0.55    inference(subsumption_resolution,[],[f300,f43])).
% 1.44/0.55  fof(f300,plain,(
% 1.44/0.55    ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK9(sK3,sK4,sK0),sK3)),
% 1.44/0.55    inference(superposition,[],[f73,f286])).
% 1.44/0.55  fof(f73,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_tarski(sK0)) | r2_hidden(X0,sK3)) )),
% 1.44/0.55    inference(resolution,[],[f38,f67])).
% 1.44/0.55  fof(f67,plain,(
% 1.44/0.55    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 1.44/0.55    inference(superposition,[],[f45,f63])).
% 1.44/0.55  fof(f63,plain,(
% 1.44/0.55    k2_zfmisc_1(sK3,sK4) = k2_xboole_0(k1_tarski(sK0),k2_zfmisc_1(sK3,sK4))),
% 1.44/0.55    inference(resolution,[],[f13,f57])).
% 1.44/0.55  fof(f335,plain,(
% 1.44/0.55    ~r2_hidden(sK9(sK3,sK4,sK0),sK3) | ~r2_hidden(sK9(sK3,sK4,sK0),sK1) | spl13_2),
% 1.44/0.55    inference(resolution,[],[f312,f47])).
% 1.44/0.55  fof(f47,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_xboole_0(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.44/0.55    inference(equality_resolution,[],[f29])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f2])).
% 1.44/0.55  fof(f312,plain,(
% 1.44/0.55    ~r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3)) | spl13_2),
% 1.44/0.55    inference(avatar_component_clause,[],[f310])).
% 1.44/0.55  fof(f310,plain,(
% 1.44/0.55    spl13_2 <=> r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.44/0.55  fof(f329,plain,(
% 1.44/0.55    spl13_1),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f328])).
% 1.44/0.55  fof(f328,plain,(
% 1.44/0.55    $false | spl13_1),
% 1.44/0.55    inference(subsumption_resolution,[],[f327,f316])).
% 1.44/0.55  fof(f316,plain,(
% 1.44/0.55    r2_hidden(sK10(sK3,sK4,sK0),sK2)),
% 1.44/0.55    inference(subsumption_resolution,[],[f303,f43])).
% 1.44/0.55  fof(f303,plain,(
% 1.44/0.55    ~r2_hidden(sK0,k1_tarski(sK0)) | r2_hidden(sK10(sK3,sK4,sK0),sK2)),
% 1.44/0.55    inference(superposition,[],[f76,f286])).
% 1.44/0.55  fof(f76,plain,(
% 1.44/0.55    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X3,X2),k1_tarski(sK0)) | r2_hidden(X2,sK2)) )),
% 1.44/0.55    inference(resolution,[],[f39,f70])).
% 1.44/0.55  fof(f39,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f5])).
% 1.44/0.55  fof(f327,plain,(
% 1.44/0.55    ~r2_hidden(sK10(sK3,sK4,sK0),sK2) | spl13_1),
% 1.44/0.55    inference(subsumption_resolution,[],[f326,f226])).
% 1.44/0.55  fof(f226,plain,(
% 1.44/0.55    r2_hidden(sK10(sK3,sK4,sK0),sK4)),
% 1.44/0.55    inference(resolution,[],[f220,f43])).
% 1.44/0.55  fof(f220,plain,(
% 1.44/0.55    ( ! [X1] : (~r2_hidden(X1,k1_tarski(sK10(sK3,sK4,sK0))) | r2_hidden(X1,sK4)) )),
% 1.44/0.55    inference(superposition,[],[f45,f213])).
% 1.44/0.55  fof(f213,plain,(
% 1.44/0.55    sK4 = k2_xboole_0(k1_tarski(sK10(sK3,sK4,sK0)),sK4)),
% 1.44/0.55    inference(resolution,[],[f86,f57])).
% 1.44/0.55  fof(f86,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k2_xboole_0(k1_tarski(sK10(X1,X2,X0)),X2) = X2) )),
% 1.44/0.55    inference(resolution,[],[f53,f13])).
% 1.44/0.55  fof(f53,plain,(
% 1.44/0.55    ( ! [X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 1.44/0.55    inference(equality_resolution,[],[f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(sK10(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.44/0.55    inference(cnf_transformation,[],[f4])).
% 1.44/0.55  fof(f326,plain,(
% 1.44/0.55    ~r2_hidden(sK10(sK3,sK4,sK0),sK4) | ~r2_hidden(sK10(sK3,sK4,sK0),sK2) | spl13_1),
% 1.44/0.55    inference(resolution,[],[f308,f47])).
% 1.44/0.55  fof(f308,plain,(
% 1.44/0.55    ~r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4)) | spl13_1),
% 1.44/0.55    inference(avatar_component_clause,[],[f306])).
% 1.44/0.55  fof(f306,plain,(
% 1.44/0.55    spl13_1 <=> r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.44/0.55  fof(f313,plain,(
% 1.44/0.55    ~spl13_1 | ~spl13_2),
% 1.44/0.55    inference(avatar_split_clause,[],[f304,f310,f306])).
% 1.44/0.55  fof(f304,plain,(
% 1.44/0.55    ~r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3)) | ~r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4))),
% 1.44/0.55    inference(trivial_inequality_removal,[],[f296])).
% 1.44/0.55  fof(f296,plain,(
% 1.44/0.55    sK0 != sK0 | ~r2_hidden(sK9(sK3,sK4,sK0),k3_xboole_0(sK1,sK3)) | ~r2_hidden(sK10(sK3,sK4,sK0),k3_xboole_0(sK2,sK4))),
% 1.44/0.55    inference(superposition,[],[f11,f286])).
% 1.44/0.55  fof(f11,plain,(
% 1.44/0.55    ( ! [X6,X5] : (k4_tarski(X5,X6) != sK0 | ~r2_hidden(X5,k3_xboole_0(sK1,sK3)) | ~r2_hidden(X6,k3_xboole_0(sK2,sK4))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f9])).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (19999)------------------------------
% 1.44/0.55  % (19999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (19999)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (19999)Memory used [KB]: 11257
% 1.44/0.55  % (19999)Time elapsed: 0.085 s
% 1.44/0.55  % (19999)------------------------------
% 1.44/0.55  % (19999)------------------------------
% 1.44/0.55  % (20002)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.44/0.55  % (19982)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.44/0.55  % (19976)Success in time 0.198 s
%------------------------------------------------------------------------------
