%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 140 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  194 ( 467 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f53,f410,f430])).

fof(f430,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f428,f51])).

fof(f51,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl7_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f428,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f426,f90])).

fof(f90,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f59,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

% (30000)Refutation not found, incomplete strategy% (30000)------------------------------
% (30000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30000)Termination reason: Refutation not found, incomplete strategy

% (30000)Memory used [KB]: 6140
% (30000)Time elapsed: 0.129 s
% (30000)------------------------------
% (30000)------------------------------
% (30018)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (30019)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (29997)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (30016)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (29996)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (30004)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (29996)Refutation not found, incomplete strategy% (29996)------------------------------
% (29996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29996)Termination reason: Refutation not found, incomplete strategy

% (29996)Memory used [KB]: 10618
% (29996)Time elapsed: 0.139 s
% (29996)------------------------------
% (29996)------------------------------
fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X2)
      | ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f426,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl7_1 ),
    inference(resolution,[],[f420,f22])).

fof(f420,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,X1),k2_relat_1(sK1))
        | r1_xboole_0(sK0,X1) )
    | ~ spl7_1 ),
    inference(resolution,[],[f418,f21])).

fof(f418,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f417,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f19,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f19,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f417,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK1,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(X1,k2_relat_1(sK1)) )
    | ~ spl7_1 ),
    inference(superposition,[],[f413,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl7_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f413,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK4(sK1,X3),k10_relat_1(sK1,X4))
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f403,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f403,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,k10_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f54,f18])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(subsumption_resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f410,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f405,f47])).

fof(f47,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f405,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f399,f156])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f155,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f37,f38])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f399,plain,
    ( ! [X0] : r1_xboole_0(k10_relat_1(sK1,sK0),X0)
    | ~ spl7_2 ),
    inference(resolution,[],[f398,f21])).

fof(f398,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
        | ~ r2_hidden(X0,k10_relat_1(sK1,sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f396,f348])).

fof(f348,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,sK1),X1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f35,f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f396,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK6(X2,X3,sK1),sK0)
        | ~ r2_hidden(X2,k10_relat_1(sK1,X3)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f394,f92])).

fof(f92,plain,
    ( r1_xboole_0(sK0,k2_relat_1(sK1))
    | ~ spl7_2 ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f394,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(X5,k2_relat_1(sK1))
      | ~ r2_hidden(sK6(X3,X4,sK1),X5)
      | ~ r2_hidden(X3,k10_relat_1(sK1,X4)) ) ),
    inference(resolution,[],[f391,f20])).

fof(f391,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,sK1),k2_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f390,f41])).

fof(f390,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X0,X1,sK1)),sK1)
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f34,f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f16,f49,f45])).

fof(f16,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f17,f49,f45])).

fof(f17,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (30008)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.50  % (30015)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.52  % (30017)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.53  % (30009)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.53  % (30006)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.53  % (30000)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.53  % (30005)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.53  % (29995)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.53  % (29995)Refutation not found, incomplete strategy% (29995)------------------------------
% 0.19/0.53  % (29995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (29995)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (29995)Memory used [KB]: 10618
% 0.19/0.53  % (29995)Time elapsed: 0.123 s
% 0.19/0.53  % (29995)------------------------------
% 0.19/0.53  % (29995)------------------------------
% 0.19/0.53  % (30007)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.54  % (29999)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.54  % (30003)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.54  % (30001)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.55  % (30002)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.55  % (30002)Refutation not found, incomplete strategy% (30002)------------------------------
% 0.19/0.55  % (30002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (30002)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (30002)Memory used [KB]: 1663
% 0.19/0.55  % (30002)Time elapsed: 0.149 s
% 0.19/0.55  % (30002)------------------------------
% 0.19/0.55  % (30002)------------------------------
% 0.19/0.55  % (29998)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.55  % (30017)Refutation found. Thanks to Tanya!
% 0.19/0.55  % SZS status Theorem for theBenchmark
% 0.19/0.55  % SZS output start Proof for theBenchmark
% 0.19/0.55  fof(f431,plain,(
% 0.19/0.55    $false),
% 0.19/0.55    inference(avatar_sat_refutation,[],[f52,f53,f410,f430])).
% 0.19/0.55  fof(f430,plain,(
% 0.19/0.55    ~spl7_1 | spl7_2),
% 0.19/0.55    inference(avatar_contradiction_clause,[],[f429])).
% 0.19/0.55  fof(f429,plain,(
% 0.19/0.55    $false | (~spl7_1 | spl7_2)),
% 0.19/0.55    inference(subsumption_resolution,[],[f428,f51])).
% 0.19/0.55  fof(f51,plain,(
% 0.19/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl7_2),
% 0.19/0.55    inference(avatar_component_clause,[],[f49])).
% 0.19/0.55  fof(f49,plain,(
% 0.19/0.55    spl7_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.19/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.19/0.55  fof(f428,plain,(
% 0.19/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl7_1),
% 0.19/0.55    inference(resolution,[],[f426,f90])).
% 0.19/0.55  fof(f90,plain,(
% 0.19/0.55    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f89])).
% 0.19/0.55  fof(f89,plain,(
% 0.19/0.55    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.19/0.55    inference(resolution,[],[f59,f22])).
% 0.19/0.55  fof(f22,plain,(
% 0.19/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f12])).
% 0.19/0.55  fof(f12,plain,(
% 0.19/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.55    inference(ennf_transformation,[],[f10])).
% 0.19/0.55  fof(f10,plain,(
% 0.19/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.55    inference(rectify,[],[f1])).
% 0.19/0.55  fof(f1,axiom,(
% 0.19/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.55  % (30000)Refutation not found, incomplete strategy% (30000)------------------------------
% 0.19/0.55  % (30000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (30000)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (30000)Memory used [KB]: 6140
% 0.19/0.55  % (30000)Time elapsed: 0.129 s
% 0.19/0.55  % (30000)------------------------------
% 0.19/0.55  % (30000)------------------------------
% 0.19/0.55  % (30018)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.55  % (30019)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.55  % (29997)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.55  % (30016)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.56  % (29996)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.56  % (30004)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.56  % (29996)Refutation not found, incomplete strategy% (29996)------------------------------
% 0.19/0.56  % (29996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (29996)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.56  
% 0.19/0.56  % (29996)Memory used [KB]: 10618
% 0.19/0.56  % (29996)Time elapsed: 0.139 s
% 0.19/0.56  % (29996)------------------------------
% 0.19/0.56  % (29996)------------------------------
% 0.19/0.56  fof(f59,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)) )),
% 0.19/0.56    inference(resolution,[],[f20,f21])).
% 0.19/0.56  fof(f21,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f12])).
% 0.19/0.56  fof(f20,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f12])).
% 0.19/0.56  fof(f426,plain,(
% 0.19/0.56    r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl7_1),
% 0.19/0.56    inference(duplicate_literal_removal,[],[f425])).
% 0.19/0.56  fof(f425,plain,(
% 0.19/0.56    r1_xboole_0(sK0,k2_relat_1(sK1)) | r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl7_1),
% 0.19/0.56    inference(resolution,[],[f420,f22])).
% 0.19/0.56  fof(f420,plain,(
% 0.19/0.56    ( ! [X1] : (~r2_hidden(sK2(sK0,X1),k2_relat_1(sK1)) | r1_xboole_0(sK0,X1)) ) | ~spl7_1),
% 0.19/0.56    inference(resolution,[],[f418,f21])).
% 0.19/0.56  fof(f418,plain,(
% 0.19/0.56    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl7_1),
% 0.19/0.56    inference(subsumption_resolution,[],[f417,f55])).
% 0.19/0.56  fof(f55,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.56    inference(superposition,[],[f19,f42])).
% 0.19/0.56  fof(f42,plain,(
% 0.19/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.56    inference(equality_resolution,[],[f32])).
% 0.19/0.56  fof(f32,plain,(
% 0.19/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f4])).
% 0.19/0.56  fof(f4,axiom,(
% 0.19/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.56  fof(f19,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f5])).
% 0.19/0.56  fof(f5,axiom,(
% 0.19/0.56    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.19/0.56  fof(f417,plain,(
% 0.19/0.56    ( ! [X1] : (r2_hidden(sK4(sK1,X1),k1_xboole_0) | ~r2_hidden(X1,sK0) | ~r2_hidden(X1,k2_relat_1(sK1))) ) | ~spl7_1),
% 0.19/0.56    inference(superposition,[],[f413,f46])).
% 0.19/0.56  fof(f46,plain,(
% 0.19/0.56    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl7_1),
% 0.19/0.56    inference(avatar_component_clause,[],[f45])).
% 0.19/0.56  fof(f45,plain,(
% 0.19/0.56    spl7_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.56  fof(f413,plain,(
% 0.19/0.56    ( ! [X4,X3] : (r2_hidden(sK4(sK1,X3),k10_relat_1(sK1,X4)) | ~r2_hidden(X3,X4) | ~r2_hidden(X3,k2_relat_1(sK1))) )),
% 0.19/0.56    inference(resolution,[],[f403,f40])).
% 0.19/0.56  fof(f40,plain,(
% 0.19/0.56    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.19/0.56    inference(equality_resolution,[],[f27])).
% 0.19/0.56  fof(f27,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f6])).
% 0.19/0.56  fof(f6,axiom,(
% 0.19/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.19/0.56  fof(f403,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,X2) | r2_hidden(X0,k10_relat_1(sK1,X2))) )),
% 0.19/0.56    inference(resolution,[],[f54,f18])).
% 0.19/0.56  fof(f18,plain,(
% 0.19/0.56    v1_relat_1(sK1)),
% 0.19/0.56    inference(cnf_transformation,[],[f11])).
% 0.19/0.56  fof(f11,plain,(
% 0.19/0.56    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.19/0.56    inference(ennf_transformation,[],[f9])).
% 0.19/0.56  fof(f9,negated_conjecture,(
% 0.19/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.19/0.56    inference(negated_conjecture,[],[f8])).
% 0.19/0.56  fof(f8,conjecture,(
% 0.19/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.19/0.56  fof(f54,plain,(
% 0.19/0.56    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f36,f41])).
% 0.19/0.56  fof(f41,plain,(
% 0.19/0.56    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.19/0.56    inference(equality_resolution,[],[f26])).
% 0.19/0.56  fof(f26,plain,(
% 0.19/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f6])).
% 0.19/0.56  fof(f36,plain,(
% 0.19/0.56    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f13])).
% 0.19/0.56  fof(f13,plain,(
% 0.19/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.56    inference(ennf_transformation,[],[f7])).
% 0.19/0.56  fof(f7,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.19/0.56  fof(f410,plain,(
% 0.19/0.56    spl7_1 | ~spl7_2),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f409])).
% 0.19/0.56  fof(f409,plain,(
% 0.19/0.56    $false | (spl7_1 | ~spl7_2)),
% 0.19/0.56    inference(subsumption_resolution,[],[f405,f47])).
% 0.19/0.56  fof(f47,plain,(
% 0.19/0.56    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl7_1),
% 0.19/0.56    inference(avatar_component_clause,[],[f45])).
% 0.19/0.56  fof(f405,plain,(
% 0.19/0.56    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl7_2),
% 0.19/0.56    inference(resolution,[],[f399,f156])).
% 0.19/0.56  fof(f156,plain,(
% 0.19/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.19/0.56    inference(resolution,[],[f155,f38])).
% 0.19/0.56  fof(f38,plain,(
% 0.19/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.56    inference(equality_resolution,[],[f24])).
% 0.19/0.56  fof(f24,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f2])).
% 0.19/0.56  fof(f2,axiom,(
% 0.19/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.56  fof(f155,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X0) | k1_xboole_0 = X0) )),
% 0.19/0.56    inference(resolution,[],[f37,f38])).
% 0.19/0.56  fof(f37,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 0.19/0.56    inference(cnf_transformation,[],[f15])).
% 0.19/0.56  fof(f15,plain,(
% 0.19/0.56    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.56    inference(flattening,[],[f14])).
% 0.19/0.56  fof(f14,plain,(
% 0.19/0.56    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.56    inference(ennf_transformation,[],[f3])).
% 0.19/0.56  fof(f3,axiom,(
% 0.19/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.19/0.56  fof(f399,plain,(
% 0.19/0.56    ( ! [X0] : (r1_xboole_0(k10_relat_1(sK1,sK0),X0)) ) | ~spl7_2),
% 0.19/0.56    inference(resolution,[],[f398,f21])).
% 0.19/0.56  fof(f398,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,sK0))) ) | ~spl7_2),
% 0.19/0.56    inference(duplicate_literal_removal,[],[f397])).
% 0.19/0.56  fof(f397,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,sK0)) | ~r2_hidden(X0,k10_relat_1(sK1,sK0))) ) | ~spl7_2),
% 0.19/0.56    inference(resolution,[],[f396,f348])).
% 0.19/0.56  fof(f348,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,sK1),X1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.19/0.56    inference(resolution,[],[f35,f18])).
% 0.19/0.56  fof(f35,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f13])).
% 0.19/0.56  fof(f396,plain,(
% 0.19/0.56    ( ! [X2,X3] : (~r2_hidden(sK6(X2,X3,sK1),sK0) | ~r2_hidden(X2,k10_relat_1(sK1,X3))) ) | ~spl7_2),
% 0.19/0.56    inference(resolution,[],[f394,f92])).
% 0.19/0.56  fof(f92,plain,(
% 0.19/0.56    r1_xboole_0(sK0,k2_relat_1(sK1)) | ~spl7_2),
% 0.19/0.56    inference(resolution,[],[f90,f50])).
% 0.19/0.56  fof(f50,plain,(
% 0.19/0.56    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl7_2),
% 0.19/0.56    inference(avatar_component_clause,[],[f49])).
% 0.19/0.56  fof(f394,plain,(
% 0.19/0.56    ( ! [X4,X5,X3] : (~r1_xboole_0(X5,k2_relat_1(sK1)) | ~r2_hidden(sK6(X3,X4,sK1),X5) | ~r2_hidden(X3,k10_relat_1(sK1,X4))) )),
% 0.19/0.56    inference(resolution,[],[f391,f20])).
% 0.19/0.56  fof(f391,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,sK1),k2_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.19/0.56    inference(resolution,[],[f390,f41])).
% 0.19/0.56  fof(f390,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,sK1)),sK1) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 0.19/0.56    inference(resolution,[],[f34,f18])).
% 0.19/0.56  fof(f34,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.19/0.56    inference(cnf_transformation,[],[f13])).
% 0.19/0.56  fof(f53,plain,(
% 0.19/0.56    spl7_1 | spl7_2),
% 0.19/0.56    inference(avatar_split_clause,[],[f16,f49,f45])).
% 0.19/0.56  fof(f16,plain,(
% 0.19/0.56    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.19/0.56    inference(cnf_transformation,[],[f11])).
% 0.19/0.56  fof(f52,plain,(
% 0.19/0.56    ~spl7_1 | ~spl7_2),
% 0.19/0.56    inference(avatar_split_clause,[],[f17,f49,f45])).
% 0.19/0.56  fof(f17,plain,(
% 0.19/0.56    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 0.19/0.56    inference(cnf_transformation,[],[f11])).
% 0.19/0.56  % SZS output end Proof for theBenchmark
% 0.19/0.56  % (30017)------------------------------
% 0.19/0.56  % (30017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.56  % (30017)Termination reason: Refutation
% 0.19/0.56  
% 0.19/0.56  % (30017)Memory used [KB]: 10746
% 0.19/0.56  % (30017)Time elapsed: 0.077 s
% 0.19/0.56  % (30017)------------------------------
% 0.19/0.56  % (30017)------------------------------
% 0.19/0.56  % (29994)Success in time 0.209 s
%------------------------------------------------------------------------------
