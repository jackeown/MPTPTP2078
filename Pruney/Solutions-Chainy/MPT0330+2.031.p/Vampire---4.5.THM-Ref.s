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
% DateTime   : Thu Dec  3 12:43:03 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 120 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  158 ( 258 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f62,f67,f199,f210,f234,f275,f312,f319,f344])).

fof(f344,plain,(
    spl6_23 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f36,f311,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f311,plain,
    ( ~ r1_tarski(sK5,k2_xboole_0(sK3,sK5))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl6_23
  <=> r1_tarski(sK5,k2_xboole_0(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f319,plain,(
    spl6_22 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl6_22 ),
    inference(unit_resulting_resolution,[],[f36,f307,f31])).

fof(f307,plain,
    ( ~ r1_tarski(sK4,k2_xboole_0(sK2,sK4))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl6_22
  <=> r1_tarski(sK4,k2_xboole_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f312,plain,
    ( ~ spl6_22
    | ~ spl6_23
    | spl6_18 ),
    inference(avatar_split_clause,[],[f302,f272,f309,f305])).

fof(f272,plain,
    ( spl6_18
  <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f302,plain,
    ( ~ r1_tarski(sK5,k2_xboole_0(sK3,sK5))
    | ~ r1_tarski(sK4,k2_xboole_0(sK2,sK4))
    | spl6_18 ),
    inference(resolution,[],[f274,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f274,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f272])).

% (32242)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f275,plain,
    ( ~ spl6_18
    | ~ spl6_4
    | spl6_11 ),
    inference(avatar_split_clause,[],[f268,f196,f59,f272])).

fof(f59,plain,
    ( spl6_4
  <=> k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f196,plain,
    ( spl6_11
  <=> r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f268,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ spl6_4
    | spl6_11 ),
    inference(superposition,[],[f262,f61])).

fof(f61,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f262,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_11 ),
    inference(resolution,[],[f198,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f198,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f234,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f25,f25,f209,f35])).

fof(f209,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl6_12
  <=> r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f210,plain,
    ( ~ spl6_12
    | ~ spl6_5
    | spl6_10 ),
    inference(avatar_split_clause,[],[f203,f192,f64,f207])).

fof(f64,plain,
    ( spl6_5
  <=> k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f192,plain,
    ( spl6_10
  <=> r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f203,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ spl6_5
    | spl6_10 ),
    inference(superposition,[],[f200,f66])).

fof(f66,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f200,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_10 ),
    inference(resolution,[],[f194,f33])).

fof(f194,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f192])).

fof(f199,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | spl6_1 ),
    inference(avatar_split_clause,[],[f162,f39,f196,f192])).

fof(f39,plain,
    ( spl6_1
  <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f162,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_1 ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f67,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f54,f49,f64])).

fof(f49,plain,
    ( spl6_3
  <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f54,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_3 ),
    inference(resolution,[],[f27,f51])).

fof(f51,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,
    ( spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f53,f44,f59])).

fof(f44,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f53,plain,
    ( k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(resolution,[],[f27,f46])).

fof(f46,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f52,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f47,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f24,f39])).

fof(f24,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (32233)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.48  % (32241)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.49  % (32235)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (32227)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (32226)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (32243)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (32229)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (32223)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (32238)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (32230)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (32225)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (32231)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (32228)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (32221)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (32232)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (32224)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (32222)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (32236)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.32/0.53  % (32239)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.32/0.53  % (32236)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % (32246)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.32/0.53  % (32237)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.32/0.53  % (32240)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.32/0.54  % (32234)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.43/0.55  % (32245)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.43/0.55  % SZS output start Proof for theBenchmark
% 1.43/0.55  fof(f355,plain,(
% 1.43/0.55    $false),
% 1.43/0.55    inference(avatar_sat_refutation,[],[f42,f47,f52,f62,f67,f199,f210,f234,f275,f312,f319,f344])).
% 1.43/0.55  fof(f344,plain,(
% 1.43/0.55    spl6_23),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f339])).
% 1.43/0.55  fof(f339,plain,(
% 1.43/0.55    $false | spl6_23),
% 1.43/0.55    inference(unit_resulting_resolution,[],[f36,f311,f31])).
% 1.43/0.55  fof(f31,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f15])).
% 1.43/0.55  fof(f15,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.43/0.55    inference(ennf_transformation,[],[f2])).
% 1.43/0.55  fof(f2,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.43/0.55  fof(f311,plain,(
% 1.43/0.55    ~r1_tarski(sK5,k2_xboole_0(sK3,sK5)) | spl6_23),
% 1.43/0.55    inference(avatar_component_clause,[],[f309])).
% 1.43/0.55  fof(f309,plain,(
% 1.43/0.55    spl6_23 <=> r1_tarski(sK5,k2_xboole_0(sK3,sK5))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.43/0.55  fof(f36,plain,(
% 1.43/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.55    inference(equality_resolution,[],[f29])).
% 1.43/0.55  fof(f29,plain,(
% 1.43/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.43/0.55    inference(cnf_transformation,[],[f1])).
% 1.43/0.55  fof(f1,axiom,(
% 1.43/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.55  fof(f319,plain,(
% 1.43/0.55    spl6_22),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f314])).
% 1.43/0.55  fof(f314,plain,(
% 1.43/0.55    $false | spl6_22),
% 1.43/0.55    inference(unit_resulting_resolution,[],[f36,f307,f31])).
% 1.43/0.55  fof(f307,plain,(
% 1.43/0.55    ~r1_tarski(sK4,k2_xboole_0(sK2,sK4)) | spl6_22),
% 1.43/0.55    inference(avatar_component_clause,[],[f305])).
% 1.43/0.55  fof(f305,plain,(
% 1.43/0.55    spl6_22 <=> r1_tarski(sK4,k2_xboole_0(sK2,sK4))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.43/0.55  fof(f312,plain,(
% 1.43/0.55    ~spl6_22 | ~spl6_23 | spl6_18),
% 1.43/0.55    inference(avatar_split_clause,[],[f302,f272,f309,f305])).
% 1.43/0.55  fof(f272,plain,(
% 1.43/0.55    spl6_18 <=> r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.43/0.55  fof(f302,plain,(
% 1.43/0.55    ~r1_tarski(sK5,k2_xboole_0(sK3,sK5)) | ~r1_tarski(sK4,k2_xboole_0(sK2,sK4)) | spl6_18),
% 1.43/0.55    inference(resolution,[],[f274,f35])).
% 1.43/0.55  fof(f35,plain,(
% 1.43/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f21])).
% 1.43/0.55  fof(f21,plain,(
% 1.43/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.43/0.55    inference(flattening,[],[f20])).
% 1.43/0.55  fof(f20,plain,(
% 1.43/0.55    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.43/0.55    inference(ennf_transformation,[],[f9])).
% 1.43/0.55  fof(f9,axiom,(
% 1.43/0.55    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 1.43/0.55  fof(f274,plain,(
% 1.43/0.55    ~r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_18),
% 1.43/0.55    inference(avatar_component_clause,[],[f272])).
% 1.43/0.55  % (32242)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.43/0.55  fof(f275,plain,(
% 1.43/0.55    ~spl6_18 | ~spl6_4 | spl6_11),
% 1.43/0.55    inference(avatar_split_clause,[],[f268,f196,f59,f272])).
% 1.43/0.55  fof(f59,plain,(
% 1.43/0.55    spl6_4 <=> k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.43/0.55  fof(f196,plain,(
% 1.43/0.55    spl6_11 <=> r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.43/0.55  fof(f268,plain,(
% 1.43/0.55    ~r1_tarski(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | (~spl6_4 | spl6_11)),
% 1.43/0.55    inference(superposition,[],[f262,f61])).
% 1.43/0.55  fof(f61,plain,(
% 1.43/0.55    k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_4),
% 1.43/0.55    inference(avatar_component_clause,[],[f59])).
% 1.43/0.55  fof(f262,plain,(
% 1.43/0.55    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK1,X0),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))) ) | spl6_11),
% 1.43/0.55    inference(resolution,[],[f198,f33])).
% 1.43/0.55  fof(f33,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f17])).
% 1.43/0.55  fof(f17,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.43/0.55    inference(ennf_transformation,[],[f3])).
% 1.43/0.55  fof(f3,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.43/0.55  fof(f198,plain,(
% 1.43/0.55    ~r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_11),
% 1.43/0.55    inference(avatar_component_clause,[],[f196])).
% 1.43/0.55  fof(f234,plain,(
% 1.43/0.55    spl6_12),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f229])).
% 1.43/0.55  fof(f229,plain,(
% 1.43/0.55    $false | spl6_12),
% 1.43/0.55    inference(unit_resulting_resolution,[],[f25,f25,f209,f35])).
% 1.43/0.55  fof(f209,plain,(
% 1.43/0.55    ~r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_12),
% 1.43/0.55    inference(avatar_component_clause,[],[f207])).
% 1.43/0.55  fof(f207,plain,(
% 1.43/0.55    spl6_12 <=> r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.43/0.55  fof(f25,plain,(
% 1.43/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f7])).
% 1.43/0.55  fof(f7,axiom,(
% 1.43/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.43/0.55  fof(f210,plain,(
% 1.43/0.55    ~spl6_12 | ~spl6_5 | spl6_10),
% 1.43/0.55    inference(avatar_split_clause,[],[f203,f192,f64,f207])).
% 1.43/0.55  fof(f64,plain,(
% 1.43/0.55    spl6_5 <=> k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.43/0.55  fof(f192,plain,(
% 1.43/0.55    spl6_10 <=> r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.43/0.55  fof(f203,plain,(
% 1.43/0.55    ~r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | (~spl6_5 | spl6_10)),
% 1.43/0.55    inference(superposition,[],[f200,f66])).
% 1.43/0.55  fof(f66,plain,(
% 1.43/0.55    k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_5),
% 1.43/0.55    inference(avatar_component_clause,[],[f64])).
% 1.43/0.55  fof(f200,plain,(
% 1.43/0.55    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))) ) | spl6_10),
% 1.43/0.55    inference(resolution,[],[f194,f33])).
% 1.43/0.55  fof(f194,plain,(
% 1.43/0.55    ~r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_10),
% 1.43/0.55    inference(avatar_component_clause,[],[f192])).
% 1.43/0.55  fof(f199,plain,(
% 1.43/0.55    ~spl6_10 | ~spl6_11 | spl6_1),
% 1.43/0.55    inference(avatar_split_clause,[],[f162,f39,f196,f192])).
% 1.43/0.55  fof(f39,plain,(
% 1.43/0.55    spl6_1 <=> r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.43/0.55  fof(f162,plain,(
% 1.43/0.55    ~r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | ~r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_1),
% 1.43/0.55    inference(resolution,[],[f34,f41])).
% 1.43/0.55  fof(f41,plain,(
% 1.43/0.55    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | spl6_1),
% 1.43/0.55    inference(avatar_component_clause,[],[f39])).
% 1.43/0.55  fof(f34,plain,(
% 1.43/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f19])).
% 1.43/0.55  fof(f19,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.43/0.55    inference(flattening,[],[f18])).
% 1.43/0.55  fof(f18,plain,(
% 1.43/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.43/0.55    inference(ennf_transformation,[],[f8])).
% 1.43/0.55  fof(f8,axiom,(
% 1.43/0.55    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.43/0.55  fof(f67,plain,(
% 1.43/0.55    spl6_5 | ~spl6_3),
% 1.43/0.55    inference(avatar_split_clause,[],[f54,f49,f64])).
% 1.43/0.55  fof(f49,plain,(
% 1.43/0.55    spl6_3 <=> r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.43/0.55  fof(f54,plain,(
% 1.43/0.55    k2_zfmisc_1(sK2,sK3) = k2_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_3),
% 1.43/0.55    inference(resolution,[],[f27,f51])).
% 1.43/0.55  fof(f51,plain,(
% 1.43/0.55    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | ~spl6_3),
% 1.43/0.55    inference(avatar_component_clause,[],[f49])).
% 1.43/0.55  fof(f27,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.43/0.55    inference(cnf_transformation,[],[f14])).
% 1.43/0.55  fof(f14,plain,(
% 1.43/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.55    inference(ennf_transformation,[],[f4])).
% 1.43/0.55  fof(f4,axiom,(
% 1.43/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.43/0.55  fof(f62,plain,(
% 1.43/0.55    spl6_4 | ~spl6_2),
% 1.43/0.55    inference(avatar_split_clause,[],[f53,f44,f59])).
% 1.43/0.55  fof(f44,plain,(
% 1.43/0.55    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.43/0.55  fof(f53,plain,(
% 1.43/0.55    k2_zfmisc_1(sK4,sK5) = k2_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 1.43/0.55    inference(resolution,[],[f27,f46])).
% 1.43/0.55  fof(f46,plain,(
% 1.43/0.55    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~spl6_2),
% 1.43/0.55    inference(avatar_component_clause,[],[f44])).
% 1.43/0.55  fof(f52,plain,(
% 1.43/0.55    spl6_3),
% 1.43/0.55    inference(avatar_split_clause,[],[f22,f49])).
% 1.43/0.55  fof(f22,plain,(
% 1.43/0.55    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.43/0.55    inference(cnf_transformation,[],[f13])).
% 1.43/0.55  fof(f13,plain,(
% 1.43/0.55    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.43/0.55    inference(flattening,[],[f12])).
% 1.43/0.55  fof(f12,plain,(
% 1.43/0.55    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.43/0.55    inference(ennf_transformation,[],[f11])).
% 1.43/0.55  fof(f11,negated_conjecture,(
% 1.43/0.55    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.43/0.55    inference(negated_conjecture,[],[f10])).
% 1.43/0.55  fof(f10,conjecture,(
% 1.43/0.55    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.43/0.55  fof(f47,plain,(
% 1.43/0.55    spl6_2),
% 1.43/0.55    inference(avatar_split_clause,[],[f23,f44])).
% 1.43/0.55  fof(f23,plain,(
% 1.43/0.55    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.43/0.55    inference(cnf_transformation,[],[f13])).
% 1.43/0.55  fof(f42,plain,(
% 1.43/0.55    ~spl6_1),
% 1.43/0.55    inference(avatar_split_clause,[],[f24,f39])).
% 1.43/0.55  fof(f24,plain,(
% 1.43/0.55    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.43/0.55    inference(cnf_transformation,[],[f13])).
% 1.43/0.55  % SZS output end Proof for theBenchmark
% 1.43/0.55  % (32236)------------------------------
% 1.43/0.55  % (32236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (32236)Termination reason: Refutation
% 1.43/0.55  
% 1.43/0.55  % (32236)Memory used [KB]: 6396
% 1.43/0.55  % (32236)Time elapsed: 0.129 s
% 1.43/0.55  % (32236)------------------------------
% 1.43/0.55  % (32236)------------------------------
% 1.43/0.56  % (32220)Success in time 0.191 s
%------------------------------------------------------------------------------
