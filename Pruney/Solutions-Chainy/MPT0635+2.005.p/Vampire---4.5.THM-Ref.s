%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:19 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 125 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  189 ( 394 expanded)
%              Number of equality atoms :   14 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f988,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f907,f941,f955,f987])).

fof(f987,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f986])).

fof(f986,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f985,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f985,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f984,f21])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f984,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f983,f26])).

% (18818)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f26,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f983,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl5_5 ),
    inference(subsumption_resolution,[],[f970,f25])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f970,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl5_5 ),
    inference(resolution,[],[f906,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f906,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f904])).

fof(f904,plain,
    ( spl5_5
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f955,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f954])).

fof(f954,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f953,f22])).

fof(f953,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f952,f21])).

fof(f952,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f951,f26])).

fof(f951,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f945,f25])).

fof(f945,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl5_4 ),
    inference(resolution,[],[f902,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f902,plain,
    ( ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl5_4
  <=> v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f941,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f940])).

fof(f940,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f939,f105])).

fof(f105,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    inference(subsumption_resolution,[],[f104,f22])).

fof(f104,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    inference(subsumption_resolution,[],[f100,f21])).

fof(f100,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f87,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f23,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f23,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f939,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f938,f88])).

fof(f88,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f23,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f938,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f917,f21])).

fof(f917,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | spl5_3 ),
    inference(resolution,[],[f898,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

% (18798)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f898,plain,
    ( ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(k6_relat_1(sK1),sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f896])).

fof(f896,plain,
    ( spl5_3
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(k6_relat_1(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f907,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f199,f904,f900,f896])).

fof(f199,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | ~ r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(k6_relat_1(sK1),sK2)) ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | sQ4_eqProxy(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f34,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,(
    ~ sQ4_eqProxy(k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0),k1_funct_1(sK2,sK0)) ),
    inference(resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | sQ4_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f49])).

fof(f52,plain,(
    ~ sQ4_eqProxy(k1_funct_1(sK2,sK0),k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)) ),
    inference(equality_proxy_replacement,[],[f24,f49])).

fof(f24,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:50:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (18801)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (18793)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (18789)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (18810)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (18810)Refutation not found, incomplete strategy% (18810)------------------------------
% 0.22/0.53  % (18810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18810)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18810)Memory used [KB]: 10746
% 0.22/0.53  % (18810)Time elapsed: 0.129 s
% 0.22/0.53  % (18810)------------------------------
% 0.22/0.53  % (18810)------------------------------
% 0.22/0.54  % (18797)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (18788)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (18792)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (18791)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (18803)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (18800)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (18817)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (18809)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (18816)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (18796)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (18795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (18807)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (18790)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.56  % (18805)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (18790)Refutation not found, incomplete strategy% (18790)------------------------------
% 1.41/0.56  % (18790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (18790)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (18790)Memory used [KB]: 10618
% 1.41/0.56  % (18790)Time elapsed: 0.145 s
% 1.41/0.56  % (18790)------------------------------
% 1.41/0.56  % (18790)------------------------------
% 1.41/0.56  % (18804)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.56  % (18808)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (18799)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.56  % (18808)Refutation not found, incomplete strategy% (18808)------------------------------
% 1.41/0.56  % (18808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (18808)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (18808)Memory used [KB]: 10746
% 1.41/0.56  % (18808)Time elapsed: 0.150 s
% 1.41/0.56  % (18808)------------------------------
% 1.41/0.56  % (18808)------------------------------
% 1.41/0.56  % (18814)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.56  % (18806)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (18801)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f988,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(avatar_sat_refutation,[],[f907,f941,f955,f987])).
% 1.41/0.56  fof(f987,plain,(
% 1.41/0.56    spl5_5),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f986])).
% 1.41/0.56  fof(f986,plain,(
% 1.41/0.56    $false | spl5_5),
% 1.41/0.56    inference(subsumption_resolution,[],[f985,f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    v1_funct_1(sK2)),
% 1.41/0.56    inference(cnf_transformation,[],[f13])).
% 1.41/0.56  fof(f13,plain,(
% 1.41/0.56    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.41/0.56    inference(flattening,[],[f12])).
% 1.41/0.56  fof(f12,plain,(
% 1.41/0.56    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.41/0.56    inference(ennf_transformation,[],[f11])).
% 1.41/0.56  fof(f11,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 1.41/0.56    inference(negated_conjecture,[],[f10])).
% 1.41/0.56  fof(f10,conjecture,(
% 1.41/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).
% 1.41/0.56  fof(f985,plain,(
% 1.41/0.56    ~v1_funct_1(sK2) | spl5_5),
% 1.41/0.56    inference(subsumption_resolution,[],[f984,f21])).
% 1.41/0.57  fof(f21,plain,(
% 1.41/0.57    v1_relat_1(sK2)),
% 1.41/0.57    inference(cnf_transformation,[],[f13])).
% 1.41/0.57  fof(f984,plain,(
% 1.41/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | spl5_5),
% 1.41/0.57    inference(subsumption_resolution,[],[f983,f26])).
% 1.41/0.57  % (18818)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.57  fof(f26,plain,(
% 1.41/0.57    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f8])).
% 1.41/0.57  fof(f8,axiom,(
% 1.41/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.41/0.57  fof(f983,plain,(
% 1.41/0.57    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | spl5_5),
% 1.41/0.57    inference(subsumption_resolution,[],[f970,f25])).
% 1.41/0.57  fof(f25,plain,(
% 1.41/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f8])).
% 1.41/0.57  fof(f970,plain,(
% 1.41/0.57    ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | spl5_5),
% 1.41/0.57    inference(resolution,[],[f906,f30])).
% 1.41/0.57  fof(f30,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f15])).
% 1.41/0.57  fof(f15,plain,(
% 1.41/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.57    inference(flattening,[],[f14])).
% 1.41/0.57  fof(f14,plain,(
% 1.41/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.57    inference(ennf_transformation,[],[f7])).
% 1.41/0.57  fof(f7,axiom,(
% 1.41/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.41/0.57  fof(f906,plain,(
% 1.41/0.57    ~v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2)) | spl5_5),
% 1.41/0.57    inference(avatar_component_clause,[],[f904])).
% 1.41/0.57  fof(f904,plain,(
% 1.41/0.57    spl5_5 <=> v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.41/0.57  fof(f955,plain,(
% 1.41/0.57    spl5_4),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f954])).
% 1.41/0.57  fof(f954,plain,(
% 1.41/0.57    $false | spl5_4),
% 1.41/0.57    inference(subsumption_resolution,[],[f953,f22])).
% 1.41/0.57  fof(f953,plain,(
% 1.41/0.57    ~v1_funct_1(sK2) | spl5_4),
% 1.41/0.57    inference(subsumption_resolution,[],[f952,f21])).
% 1.41/0.57  fof(f952,plain,(
% 1.41/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | spl5_4),
% 1.41/0.57    inference(subsumption_resolution,[],[f951,f26])).
% 1.41/0.57  fof(f951,plain,(
% 1.41/0.57    ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | spl5_4),
% 1.41/0.57    inference(subsumption_resolution,[],[f945,f25])).
% 1.41/0.57  fof(f945,plain,(
% 1.41/0.57    ~v1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | spl5_4),
% 1.41/0.57    inference(resolution,[],[f902,f31])).
% 1.41/0.57  fof(f31,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(X0,X1))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f15])).
% 1.41/0.57  fof(f902,plain,(
% 1.41/0.57    ~v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2)) | spl5_4),
% 1.41/0.57    inference(avatar_component_clause,[],[f900])).
% 1.41/0.57  fof(f900,plain,(
% 1.41/0.57    spl5_4 <=> v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2))),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.41/0.57  fof(f941,plain,(
% 1.41/0.57    spl5_3),
% 1.41/0.57    inference(avatar_contradiction_clause,[],[f940])).
% 1.41/0.57  fof(f940,plain,(
% 1.41/0.57    $false | spl5_3),
% 1.41/0.57    inference(subsumption_resolution,[],[f939,f105])).
% 1.41/0.57  fof(f105,plain,(
% 1.41/0.57    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 1.41/0.57    inference(subsumption_resolution,[],[f104,f22])).
% 1.41/0.57  fof(f104,plain,(
% 1.41/0.57    ~v1_funct_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 1.41/0.57    inference(subsumption_resolution,[],[f100,f21])).
% 1.41/0.57  fof(f100,plain,(
% 1.41/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 1.41/0.57    inference(resolution,[],[f87,f45])).
% 1.41/0.57  fof(f45,plain,(
% 1.41/0.57    ( ! [X2,X0] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 1.41/0.57    inference(equality_resolution,[],[f35])).
% 1.41/0.57  fof(f35,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f19])).
% 1.41/0.57  fof(f19,plain,(
% 1.41/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.41/0.57    inference(flattening,[],[f18])).
% 1.41/0.57  fof(f18,plain,(
% 1.41/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.41/0.57    inference(ennf_transformation,[],[f9])).
% 1.41/0.57  fof(f9,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.41/0.57  fof(f87,plain,(
% 1.41/0.57    r2_hidden(sK0,k1_relat_1(sK2))),
% 1.41/0.57    inference(resolution,[],[f23,f48])).
% 1.41/0.57  fof(f48,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.41/0.57    inference(equality_resolution,[],[f39])).
% 1.41/0.57  fof(f39,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.41/0.57    inference(cnf_transformation,[],[f1])).
% 1.41/0.57  fof(f1,axiom,(
% 1.41/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.41/0.57  fof(f23,plain,(
% 1.41/0.57    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 1.41/0.57    inference(cnf_transformation,[],[f13])).
% 1.41/0.57  fof(f939,plain,(
% 1.41/0.57    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | spl5_3),
% 1.41/0.57    inference(subsumption_resolution,[],[f938,f88])).
% 1.41/0.57  fof(f88,plain,(
% 1.41/0.57    r2_hidden(sK0,sK1)),
% 1.41/0.57    inference(resolution,[],[f23,f47])).
% 1.41/0.57  fof(f47,plain,(
% 1.41/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.41/0.57    inference(equality_resolution,[],[f40])).
% 1.41/0.57  fof(f40,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.41/0.57    inference(cnf_transformation,[],[f1])).
% 1.41/0.57  fof(f938,plain,(
% 1.41/0.57    ~r2_hidden(sK0,sK1) | ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | spl5_3),
% 1.41/0.57    inference(subsumption_resolution,[],[f917,f21])).
% 1.41/0.57  fof(f917,plain,(
% 1.41/0.57    ~v1_relat_1(sK2) | ~r2_hidden(sK0,sK1) | ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | spl5_3),
% 1.41/0.57    inference(resolution,[],[f898,f44])).
% 1.41/0.57  fof(f44,plain,(
% 1.41/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) )),
% 1.41/0.57    inference(cnf_transformation,[],[f20])).
% 1.41/0.57  fof(f20,plain,(
% 1.41/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 1.41/0.57    inference(ennf_transformation,[],[f6])).
% 1.41/0.57  fof(f6,axiom,(
% 1.41/0.57    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 1.41/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
% 1.41/0.57  % (18798)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.57  fof(f898,plain,(
% 1.41/0.57    ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(k6_relat_1(sK1),sK2)) | spl5_3),
% 1.41/0.57    inference(avatar_component_clause,[],[f896])).
% 1.41/0.57  fof(f896,plain,(
% 1.41/0.57    spl5_3 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(k6_relat_1(sK1),sK2))),
% 1.41/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.41/0.57  fof(f907,plain,(
% 1.41/0.57    ~spl5_3 | ~spl5_4 | ~spl5_5),
% 1.41/0.57    inference(avatar_split_clause,[],[f199,f904,f900,f896])).
% 1.41/0.57  fof(f199,plain,(
% 1.41/0.57    ~v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2)) | ~v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2)) | ~r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),k5_relat_1(k6_relat_1(sK1),sK2))),
% 1.41/0.57    inference(resolution,[],[f93,f54])).
% 1.41/0.57  fof(f54,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | sQ4_eqProxy(k1_funct_1(X2,X0),X1) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.41/0.57    inference(equality_proxy_replacement,[],[f34,f49])).
% 1.41/0.57  fof(f49,plain,(
% 1.41/0.57    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 1.41/0.57    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 1.41/0.57  fof(f34,plain,(
% 1.41/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.41/0.57    inference(cnf_transformation,[],[f19])).
% 1.41/0.57  fof(f93,plain,(
% 1.41/0.57    ~sQ4_eqProxy(k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0),k1_funct_1(sK2,sK0))),
% 1.41/0.57    inference(resolution,[],[f52,f59])).
% 1.41/0.57  fof(f59,plain,(
% 1.41/0.57    ( ! [X0,X1] : (~sQ4_eqProxy(X0,X1) | sQ4_eqProxy(X1,X0)) )),
% 1.41/0.57    inference(equality_proxy_axiom,[],[f49])).
% 1.41/0.57  fof(f52,plain,(
% 1.41/0.57    ~sQ4_eqProxy(k1_funct_1(sK2,sK0),k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0))),
% 1.41/0.57    inference(equality_proxy_replacement,[],[f24,f49])).
% 1.41/0.57  fof(f24,plain,(
% 1.41/0.57    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 1.41/0.57    inference(cnf_transformation,[],[f13])).
% 1.41/0.57  % SZS output end Proof for theBenchmark
% 1.41/0.57  % (18801)------------------------------
% 1.41/0.57  % (18801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (18801)Termination reason: Refutation
% 1.41/0.57  
% 1.41/0.57  % (18801)Memory used [KB]: 6908
% 1.41/0.57  % (18801)Time elapsed: 0.135 s
% 1.41/0.57  % (18801)------------------------------
% 1.41/0.57  % (18801)------------------------------
% 1.59/0.57  % (18787)Success in time 0.203 s
%------------------------------------------------------------------------------
