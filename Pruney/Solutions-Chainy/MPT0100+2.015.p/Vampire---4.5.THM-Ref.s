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
% DateTime   : Thu Dec  3 12:31:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 121 expanded)
%              Number of leaves         :    8 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  166 ( 298 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f108,f116,f170,f174,f263])).

fof(f263,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f261,f89])).

fof(f89,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_2
  <=> r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f261,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f249,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_3
  <=> r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f249,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_1
    | spl6_2 ),
    inference(resolution,[],[f207,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f207,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f195,f182])).

fof(f182,plain,
    ( ! [X6] : ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,X6))
    | spl6_2 ),
    inference(resolution,[],[f89,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f195,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f84,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_1
  <=> r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f174,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f88,f171])).

fof(f171,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f135,f157])).

fof(f157,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | spl6_1 ),
    inference(resolution,[],[f93,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f93,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f85,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f85,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f135,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl6_1 ),
    inference(resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f170,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f168,f106])).

fof(f106,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f168,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f157,f145])).

fof(f145,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f134,f106])).

fof(f134,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl6_1 ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,
    ( spl6_1
    | spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f64,f87,f105,f83])).

fof(f64,plain,
    ( r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f35,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ~ sQ5_eqProxy(k2_xboole_0(sK0,sK1),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f18,f49])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f108,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f63,f105,f83])).

fof(f63,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f34,f49])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f90,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f62,f87,f83])).

fof(f62,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | sQ5_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f33,f49])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31745)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.47  % (31745)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (31754)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.47  % (31754)Refutation not found, incomplete strategy% (31754)------------------------------
% 0.20/0.47  % (31754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f264,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f90,f108,f116,f170,f174,f263])).
% 0.20/0.47  fof(f263,plain,(
% 0.20/0.47    ~spl6_1 | spl6_2 | spl6_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f262])).
% 0.20/0.47  fof(f262,plain,(
% 0.20/0.47    $false | (~spl6_1 | spl6_2 | spl6_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f261,f89])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | spl6_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl6_2 <=> r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.47  fof(f261,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | (~spl6_1 | spl6_2 | spl6_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f249,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | spl6_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    spl6_3 <=> r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.47  fof(f249,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | (~spl6_1 | spl6_2)),
% 0.20/0.47    inference(resolution,[],[f207,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | (~spl6_1 | spl6_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f195,f182])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ( ! [X6] : (~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,X6))) ) | spl6_2),
% 0.20/0.47    inference(resolution,[],[f89,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | ~spl6_1),
% 0.20/0.47    inference(resolution,[],[f84,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | ~spl6_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl6_1 <=> r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    spl6_1 | ~spl6_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    $false | (spl6_1 | ~spl6_2)),
% 0.20/0.47    inference(subsumption_resolution,[],[f88,f171])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | spl6_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f135,f157])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | spl6_1),
% 0.20/0.47    inference(resolution,[],[f93,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | spl6_1),
% 0.20/0.47    inference(resolution,[],[f85,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | spl6_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f83])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | spl6_1),
% 0.20/0.47    inference(resolution,[],[f92,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | spl6_1),
% 0.20/0.47    inference(resolution,[],[f85,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(equality_resolution,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~spl6_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f87])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    spl6_1 | ~spl6_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    $false | (spl6_1 | ~spl6_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f168,f106])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | ~spl6_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f105])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | (spl6_1 | ~spl6_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f157,f145])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | (spl6_1 | ~spl6_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f134,f106])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | spl6_1),
% 0.20/0.47    inference(resolution,[],[f92,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl6_1 | spl6_3 | spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f64,f87,f105,f83])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(resolution,[],[f50,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f35,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ~sQ5_eqProxy(k2_xboole_0(sK0,sK1),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f18,f49])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f10])).
% 0.20/0.47  fof(f10,conjecture,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ~spl6_1 | ~spl6_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f63,f105,f83])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(resolution,[],[f50,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f34,f49])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ~spl6_1 | ~spl6_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f87,f83])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~r2_hidden(sK4(sK0,sK1,k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(resolution,[],[f50,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | sQ5_eqProxy(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f33,f49])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (31745)------------------------------
% 0.20/0.47  % (31745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31745)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (31745)Memory used [KB]: 6268
% 0.20/0.47  % (31745)Time elapsed: 0.063 s
% 0.20/0.47  % (31745)------------------------------
% 0.20/0.47  % (31745)------------------------------
% 0.20/0.47  % (31731)Success in time 0.116 s
%------------------------------------------------------------------------------
