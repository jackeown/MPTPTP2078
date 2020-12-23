%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:44 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 165 expanded)
%              Number of leaves         :   16 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 ( 403 expanded)
%              Number of equality atoms :   18 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2095,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f118,f142,f393,f411,f1027,f2034,f2051,f2092,f2094])).

fof(f2094,plain,
    ( spl8_3
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f2093])).

fof(f2093,plain,
    ( $false
    | spl8_3
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f406,f2062])).

fof(f2062,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | spl8_3 ),
    inference(resolution,[],[f91,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
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

fof(f91,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_3
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f406,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl8_9
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f2092,plain,
    ( spl8_3
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f2087])).

% (10066)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% (10065)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
fof(f2087,plain,
    ( $false
    | spl8_3
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f392,f141,f128,f38])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f128,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))
    | spl8_3 ),
    inference(resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f141,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_6
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f392,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl8_8
  <=> r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f2051,plain,
    ( spl8_3
    | ~ spl8_7
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f2050])).

fof(f2050,plain,
    ( $false
    | spl8_3
    | ~ spl8_7
    | spl8_9 ),
    inference(subsumption_resolution,[],[f91,f2049])).

fof(f2049,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | ~ spl8_7
    | spl8_9 ),
    inference(subsumption_resolution,[],[f2048,f45])).

fof(f45,plain,(
    ~ sQ7_eqProxy(k3_tarski(k2_xboole_0(sK0,sK1)),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(equality_proxy_replacement,[],[f14,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f14,plain,(
    k3_tarski(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) != k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f2048,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | sQ7_eqProxy(k3_tarski(k2_xboole_0(sK0,sK1)),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | ~ spl8_7
    | spl8_9 ),
    inference(subsumption_resolution,[],[f1106,f388])).

fof(f388,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl8_7
  <=> r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1106,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | sQ7_eqProxy(k3_tarski(k2_xboole_0(sK0,sK1)),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | spl8_9 ),
    inference(resolution,[],[f1032,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),sK5(X0,X1))
      | r2_hidden(sK3(X0,X1),X1)
      | sQ7_eqProxy(k3_tarski(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f24,f44])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),sK5(X0,X1))
      | r2_hidden(sK3(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1032,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0)
        | ~ r2_hidden(X0,sK1) )
    | spl8_9 ),
    inference(resolution,[],[f405,f38])).

fof(f405,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f404])).

fof(f2034,plain,
    ( ~ spl8_5
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f2033])).

fof(f2033,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f2010,f1096])).

fof(f1096,plain,
    ( ! [X0] : r2_hidden(sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,X0))
    | ~ spl8_10 ),
    inference(resolution,[],[f1037,f42])).

fof(f1037,plain,
    ( r2_hidden(sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK0)
    | ~ spl8_10 ),
    inference(resolution,[],[f410,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK4(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f410,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl8_10
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f2010,plain,
    ( ~ r2_hidden(sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(resolution,[],[f1036,f117])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK0,sK1)) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_5
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0)
        | ~ r2_hidden(X0,k2_xboole_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1036,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))))
    | ~ spl8_10 ),
    inference(resolution,[],[f410,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK4(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f1027,plain,
    ( ~ spl8_5
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f1026])).

fof(f1026,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f1022,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1022,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(resolution,[],[f987,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f987,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(resolution,[],[f980,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f980,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(resolution,[],[f475,f534])).

fof(f534,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f528])).

fof(f528,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl8_5 ),
    inference(resolution,[],[f162,f39])).

fof(f162,plain,
    ( ! [X12] :
        ( ~ r2_hidden(sK4(X12,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,sK1))
        | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(X12)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f117,f40])).

fof(f475,plain,
    ( ! [X9] :
        ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X9)
        | ~ r1_tarski(k3_tarski(sK1),X9) )
    | ~ spl8_9 ),
    inference(resolution,[],[f406,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f411,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f143,f90,f408,f404])).

fof(f143,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))
    | ~ spl8_3 ),
    inference(resolution,[],[f92,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f92,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f393,plain,
    ( spl8_7
    | spl8_8
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f119,f94,f390,f386])).

fof(f94,plain,
    ( spl8_4
  <=> r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f119,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0)
    | r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f96,f43])).

fof(f96,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f142,plain,
    ( spl8_3
    | spl8_6 ),
    inference(avatar_split_clause,[],[f57,f139,f90])).

fof(f57,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(resolution,[],[f45,f48])).

fof(f118,plain,
    ( ~ spl8_3
    | spl8_5 ),
    inference(avatar_split_clause,[],[f56,f116,f90])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0)
      | ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X3)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | sQ7_eqProxy(k3_tarski(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f23,f44])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X3)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f58,f94,f90])).

fof(f58,plain,
    ( r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | sQ7_eqProxy(k3_tarski(X0),X1) ) ),
    inference(equality_proxy_replacement,[],[f25,f44])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (10041)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (10051)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (10043)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (10057)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (10033)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (10033)Refutation not found, incomplete strategy% (10033)------------------------------
% 0.22/0.52  % (10033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10033)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10033)Memory used [KB]: 6140
% 0.22/0.52  % (10033)Time elapsed: 0.109 s
% 0.22/0.52  % (10033)------------------------------
% 0.22/0.52  % (10033)------------------------------
% 0.22/0.52  % (10051)Refutation not found, incomplete strategy% (10051)------------------------------
% 0.22/0.52  % (10051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10051)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10051)Memory used [KB]: 10618
% 0.22/0.52  % (10051)Time elapsed: 0.065 s
% 0.22/0.52  % (10051)------------------------------
% 0.22/0.52  % (10051)------------------------------
% 0.22/0.52  % (10035)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (10042)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (10044)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (10049)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (10052)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (10048)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (10040)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (10056)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (10049)Refutation not found, incomplete strategy% (10049)------------------------------
% 0.22/0.54  % (10049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10049)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10049)Memory used [KB]: 10618
% 0.22/0.54  % (10049)Time elapsed: 0.123 s
% 0.22/0.54  % (10049)------------------------------
% 0.22/0.54  % (10049)------------------------------
% 0.22/0.54  % (10054)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (10053)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (10030)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (10030)Refutation not found, incomplete strategy% (10030)------------------------------
% 0.22/0.54  % (10030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10030)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10030)Memory used [KB]: 10618
% 0.22/0.54  % (10030)Time elapsed: 0.126 s
% 0.22/0.54  % (10030)------------------------------
% 0.22/0.54  % (10030)------------------------------
% 0.22/0.55  % (10029)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (10034)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (10046)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (10031)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (10038)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (10045)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.56  % (10036)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.47/0.56  % (10028)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.56  % (10058)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.47/0.56  % (10037)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.56  % (10054)Refutation not found, incomplete strategy% (10054)------------------------------
% 1.47/0.56  % (10054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (10054)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (10054)Memory used [KB]: 6268
% 1.47/0.56  % (10054)Time elapsed: 0.149 s
% 1.47/0.56  % (10054)------------------------------
% 1.47/0.56  % (10054)------------------------------
% 1.47/0.56  % (10037)Refutation not found, incomplete strategy% (10037)------------------------------
% 1.47/0.56  % (10037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (10037)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (10037)Memory used [KB]: 10618
% 1.47/0.56  % (10037)Time elapsed: 0.149 s
% 1.47/0.56  % (10037)------------------------------
% 1.47/0.56  % (10037)------------------------------
% 1.47/0.56  % (10047)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.56  % (10050)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.57  % (10050)Refutation not found, incomplete strategy% (10050)------------------------------
% 1.47/0.57  % (10050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (10050)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (10050)Memory used [KB]: 1663
% 1.47/0.57  % (10050)Time elapsed: 0.160 s
% 1.47/0.57  % (10050)------------------------------
% 1.47/0.57  % (10050)------------------------------
% 1.47/0.57  % (10039)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.57  % (10039)Refutation not found, incomplete strategy% (10039)------------------------------
% 1.47/0.57  % (10039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (10039)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (10039)Memory used [KB]: 10618
% 1.47/0.57  % (10039)Time elapsed: 0.158 s
% 1.47/0.57  % (10039)------------------------------
% 1.47/0.57  % (10039)------------------------------
% 1.62/0.58  % (10055)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.99/0.64  % (10059)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.68  % (10062)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.68  % (10061)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.11/0.70  % (10063)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.11/0.70  % (10064)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.11/0.70  % (10060)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.54/0.72  % (10042)Refutation found. Thanks to Tanya!
% 2.54/0.72  % SZS status Theorem for theBenchmark
% 2.54/0.72  % SZS output start Proof for theBenchmark
% 2.54/0.72  fof(f2095,plain,(
% 2.54/0.72    $false),
% 2.54/0.72    inference(avatar_sat_refutation,[],[f97,f118,f142,f393,f411,f1027,f2034,f2051,f2092,f2094])).
% 2.54/0.72  fof(f2094,plain,(
% 2.54/0.72    spl8_3 | ~spl8_9),
% 2.54/0.72    inference(avatar_contradiction_clause,[],[f2093])).
% 2.54/0.72  fof(f2093,plain,(
% 2.54/0.72    $false | (spl8_3 | ~spl8_9)),
% 2.54/0.72    inference(subsumption_resolution,[],[f406,f2062])).
% 2.54/0.72  fof(f2062,plain,(
% 2.54/0.72    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1)) | spl8_3),
% 2.54/0.72    inference(resolution,[],[f91,f41])).
% 2.54/0.72  fof(f41,plain,(
% 2.54/0.72    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 2.54/0.72    inference(equality_resolution,[],[f35])).
% 2.54/0.72  fof(f35,plain,(
% 2.54/0.72    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.54/0.72    inference(cnf_transformation,[],[f2])).
% 2.54/0.72  fof(f2,axiom,(
% 2.54/0.72    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.54/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.54/0.72  fof(f91,plain,(
% 2.54/0.72    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | spl8_3),
% 2.54/0.72    inference(avatar_component_clause,[],[f90])).
% 2.54/0.72  fof(f90,plain,(
% 2.54/0.72    spl8_3 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 2.54/0.72    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.54/0.72  fof(f406,plain,(
% 2.54/0.72    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1)) | ~spl8_9),
% 2.54/0.72    inference(avatar_component_clause,[],[f404])).
% 2.54/0.72  fof(f404,plain,(
% 2.54/0.72    spl8_9 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1))),
% 2.54/0.72    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.54/0.72  fof(f2092,plain,(
% 2.54/0.72    spl8_3 | ~spl8_6 | ~spl8_8),
% 2.54/0.72    inference(avatar_contradiction_clause,[],[f2087])).
% 2.54/0.73  % (10066)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.54/0.74  % (10065)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.54/0.74  fof(f2087,plain,(
% 2.54/0.74    $false | (spl8_3 | ~spl8_6 | ~spl8_8)),
% 2.54/0.74    inference(unit_resulting_resolution,[],[f392,f141,f128,f38])).
% 2.54/0.74  fof(f38,plain,(
% 2.54/0.74    ( ! [X2,X0,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0))) )),
% 2.54/0.74    inference(equality_resolution,[],[f28])).
% 2.54/0.74  fof(f28,plain,(
% 2.54/0.74    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 2.54/0.74    inference(cnf_transformation,[],[f6])).
% 2.54/0.74  fof(f6,axiom,(
% 2.54/0.74    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.54/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 2.54/0.74  fof(f128,plain,(
% 2.54/0.74    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0)) | spl8_3),
% 2.54/0.74    inference(resolution,[],[f91,f42])).
% 2.54/0.74  fof(f42,plain,(
% 2.54/0.74    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 2.54/0.74    inference(equality_resolution,[],[f34])).
% 2.54/0.74  fof(f34,plain,(
% 2.54/0.74    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.54/0.74    inference(cnf_transformation,[],[f2])).
% 2.54/0.74  fof(f141,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) | ~spl8_6),
% 2.54/0.74    inference(avatar_component_clause,[],[f139])).
% 2.54/0.74  fof(f139,plain,(
% 2.54/0.74    spl8_6 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))),
% 2.54/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.54/0.74  fof(f392,plain,(
% 2.54/0.74    r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0) | ~spl8_8),
% 2.54/0.74    inference(avatar_component_clause,[],[f390])).
% 2.54/0.74  fof(f390,plain,(
% 2.54/0.74    spl8_8 <=> r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0)),
% 2.54/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.54/0.74  fof(f2051,plain,(
% 2.54/0.74    spl8_3 | ~spl8_7 | spl8_9),
% 2.54/0.74    inference(avatar_contradiction_clause,[],[f2050])).
% 2.54/0.74  fof(f2050,plain,(
% 2.54/0.74    $false | (spl8_3 | ~spl8_7 | spl8_9)),
% 2.54/0.74    inference(subsumption_resolution,[],[f91,f2049])).
% 2.54/0.74  fof(f2049,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | (~spl8_7 | spl8_9)),
% 2.54/0.74    inference(subsumption_resolution,[],[f2048,f45])).
% 2.54/0.74  fof(f45,plain,(
% 2.54/0.74    ~sQ7_eqProxy(k3_tarski(k2_xboole_0(sK0,sK1)),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 2.54/0.74    inference(equality_proxy_replacement,[],[f14,f44])).
% 2.54/0.74  fof(f44,plain,(
% 2.54/0.74    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 2.54/0.74    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 2.54/0.74  fof(f14,plain,(
% 2.54/0.74    k3_tarski(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),
% 2.54/0.74    inference(cnf_transformation,[],[f10])).
% 2.54/0.74  fof(f10,plain,(
% 2.54/0.74    ? [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) != k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 2.54/0.74    inference(ennf_transformation,[],[f9])).
% 2.54/0.74  fof(f9,negated_conjecture,(
% 2.54/0.74    ~! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 2.54/0.74    inference(negated_conjecture,[],[f8])).
% 2.54/0.74  fof(f8,conjecture,(
% 2.54/0.74    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 2.54/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 2.54/0.74  fof(f2048,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | sQ7_eqProxy(k3_tarski(k2_xboole_0(sK0,sK1)),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | (~spl8_7 | spl8_9)),
% 2.54/0.74    inference(subsumption_resolution,[],[f1106,f388])).
% 2.54/0.74  fof(f388,plain,(
% 2.54/0.74    r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1) | ~spl8_7),
% 2.54/0.74    inference(avatar_component_clause,[],[f386])).
% 2.54/0.74  fof(f386,plain,(
% 2.54/0.74    spl8_7 <=> r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1)),
% 2.54/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.54/0.74  fof(f1106,plain,(
% 2.54/0.74    ~r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | sQ7_eqProxy(k3_tarski(k2_xboole_0(sK0,sK1)),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | spl8_9),
% 2.54/0.74    inference(resolution,[],[f1032,f48])).
% 2.54/0.74  fof(f48,plain,(
% 2.54/0.74    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),sK5(X0,X1)) | r2_hidden(sK3(X0,X1),X1) | sQ7_eqProxy(k3_tarski(X0),X1)) )),
% 2.54/0.74    inference(equality_proxy_replacement,[],[f24,f44])).
% 2.54/0.74  fof(f24,plain,(
% 2.54/0.74    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),sK5(X0,X1)) | r2_hidden(sK3(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 2.54/0.74    inference(cnf_transformation,[],[f6])).
% 2.54/0.74  fof(f1032,plain,(
% 2.54/0.74    ( ! [X0] : (~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0) | ~r2_hidden(X0,sK1)) ) | spl8_9),
% 2.54/0.74    inference(resolution,[],[f405,f38])).
% 2.54/0.74  fof(f405,plain,(
% 2.54/0.74    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1)) | spl8_9),
% 2.54/0.74    inference(avatar_component_clause,[],[f404])).
% 2.54/0.74  fof(f2034,plain,(
% 2.54/0.74    ~spl8_5 | ~spl8_10),
% 2.54/0.74    inference(avatar_contradiction_clause,[],[f2033])).
% 2.54/0.74  fof(f2033,plain,(
% 2.54/0.74    $false | (~spl8_5 | ~spl8_10)),
% 2.54/0.74    inference(subsumption_resolution,[],[f2010,f1096])).
% 2.54/0.74  fof(f1096,plain,(
% 2.54/0.74    ( ! [X0] : (r2_hidden(sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,X0))) ) | ~spl8_10),
% 2.54/0.74    inference(resolution,[],[f1037,f42])).
% 2.54/0.74  fof(f1037,plain,(
% 2.54/0.74    r2_hidden(sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),sK0) | ~spl8_10),
% 2.54/0.74    inference(resolution,[],[f410,f39])).
% 2.54/0.74  fof(f39,plain,(
% 2.54/0.74    ( ! [X2,X0] : (r2_hidden(sK4(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 2.54/0.74    inference(equality_resolution,[],[f27])).
% 2.54/0.74  fof(f27,plain,(
% 2.54/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X2),X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 2.54/0.74    inference(cnf_transformation,[],[f6])).
% 2.54/0.74  fof(f410,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0)) | ~spl8_10),
% 2.54/0.74    inference(avatar_component_clause,[],[f408])).
% 2.54/0.74  fof(f408,plain,(
% 2.54/0.74    spl8_10 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0))),
% 2.54/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.54/0.74  fof(f2010,plain,(
% 2.54/0.74    ~r2_hidden(sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,sK1)) | (~spl8_5 | ~spl8_10)),
% 2.54/0.74    inference(resolution,[],[f1036,f117])).
% 2.54/0.74  fof(f117,plain,(
% 2.54/0.74    ( ! [X0] : (~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0) | ~r2_hidden(X0,k2_xboole_0(sK0,sK1))) ) | ~spl8_5),
% 2.54/0.74    inference(avatar_component_clause,[],[f116])).
% 2.54/0.74  fof(f116,plain,(
% 2.54/0.74    spl8_5 <=> ! [X0] : (~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0) | ~r2_hidden(X0,k2_xboole_0(sK0,sK1)))),
% 2.54/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.54/0.74  fof(f1036,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK4(sK0,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))))) | ~spl8_10),
% 2.54/0.74    inference(resolution,[],[f410,f40])).
% 2.54/0.74  fof(f40,plain,(
% 2.54/0.74    ( ! [X2,X0] : (r2_hidden(X2,sK4(X0,X2)) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 2.54/0.74    inference(equality_resolution,[],[f26])).
% 2.54/0.74  fof(f26,plain,(
% 2.54/0.74    ( ! [X2,X0,X1] : (r2_hidden(X2,sK4(X0,X2)) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 2.54/0.74    inference(cnf_transformation,[],[f6])).
% 2.54/0.74  fof(f1027,plain,(
% 2.54/0.74    ~spl8_5 | ~spl8_9),
% 2.54/0.74    inference(avatar_contradiction_clause,[],[f1026])).
% 2.54/0.74  fof(f1026,plain,(
% 2.54/0.74    $false | (~spl8_5 | ~spl8_9)),
% 2.54/0.74    inference(subsumption_resolution,[],[f1022,f37])).
% 2.54/0.74  fof(f37,plain,(
% 2.54/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.54/0.74    inference(equality_resolution,[],[f17])).
% 2.54/0.74  fof(f17,plain,(
% 2.54/0.74    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.54/0.74    inference(cnf_transformation,[],[f3])).
% 2.54/0.74  fof(f3,axiom,(
% 2.54/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.54/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.54/0.74  fof(f1022,plain,(
% 2.54/0.74    ~r1_tarski(sK1,sK1) | (~spl8_5 | ~spl8_9)),
% 2.54/0.74    inference(resolution,[],[f987,f29])).
% 2.54/0.74  fof(f29,plain,(
% 2.54/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.54/0.74    inference(cnf_transformation,[],[f13])).
% 2.54/0.74  fof(f13,plain,(
% 2.54/0.74    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.54/0.74    inference(ennf_transformation,[],[f4])).
% 2.54/0.74  fof(f4,axiom,(
% 2.54/0.74    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.54/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.54/0.74  fof(f987,plain,(
% 2.54/0.74    ~r1_tarski(sK1,k2_xboole_0(sK0,sK1)) | (~spl8_5 | ~spl8_9)),
% 2.54/0.74    inference(resolution,[],[f980,f16])).
% 2.54/0.74  fof(f16,plain,(
% 2.54/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 2.54/0.74    inference(cnf_transformation,[],[f11])).
% 2.54/0.74  fof(f11,plain,(
% 2.54/0.74    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 2.54/0.74    inference(ennf_transformation,[],[f7])).
% 2.54/0.74  fof(f7,axiom,(
% 2.54/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 2.54/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 2.54/0.74  fof(f980,plain,(
% 2.54/0.74    ~r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))) | (~spl8_5 | ~spl8_9)),
% 2.54/0.74    inference(resolution,[],[f475,f534])).
% 2.54/0.74  fof(f534,plain,(
% 2.54/0.74    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(k2_xboole_0(sK0,sK1))) | ~spl8_5),
% 2.54/0.74    inference(duplicate_literal_removal,[],[f528])).
% 2.54/0.74  fof(f528,plain,(
% 2.54/0.74    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(k2_xboole_0(sK0,sK1))) | ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(k2_xboole_0(sK0,sK1))) | ~spl8_5),
% 2.54/0.74    inference(resolution,[],[f162,f39])).
% 2.54/0.74  fof(f162,plain,(
% 2.54/0.74    ( ! [X12] : (~r2_hidden(sK4(X12,sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),k2_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(X12))) ) | ~spl8_5),
% 2.54/0.74    inference(resolution,[],[f117,f40])).
% 2.54/0.74  fof(f475,plain,(
% 2.54/0.74    ( ! [X9] : (r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X9) | ~r1_tarski(k3_tarski(sK1),X9)) ) | ~spl8_9),
% 2.54/0.74    inference(resolution,[],[f406,f20])).
% 2.54/0.74  fof(f20,plain,(
% 2.54/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.54/0.74    inference(cnf_transformation,[],[f12])).
% 2.54/0.74  fof(f12,plain,(
% 2.54/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.54/0.74    inference(ennf_transformation,[],[f1])).
% 2.54/0.74  fof(f1,axiom,(
% 2.54/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.54/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.54/0.74  fof(f411,plain,(
% 2.54/0.74    spl8_9 | spl8_10 | ~spl8_3),
% 2.54/0.74    inference(avatar_split_clause,[],[f143,f90,f408,f404])).
% 2.54/0.74  fof(f143,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK0)) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k3_tarski(sK1)) | ~spl8_3),
% 2.54/0.74    inference(resolution,[],[f92,f43])).
% 2.54/0.74  fof(f43,plain,(
% 2.54/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 2.54/0.74    inference(equality_resolution,[],[f33])).
% 2.54/0.74  fof(f33,plain,(
% 2.54/0.74    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.54/0.74    inference(cnf_transformation,[],[f2])).
% 2.54/0.74  fof(f92,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) | ~spl8_3),
% 2.54/0.74    inference(avatar_component_clause,[],[f90])).
% 2.54/0.74  fof(f393,plain,(
% 2.54/0.74    spl8_7 | spl8_8 | ~spl8_4),
% 2.54/0.74    inference(avatar_split_clause,[],[f119,f94,f390,f386])).
% 2.54/0.74  fof(f94,plain,(
% 2.54/0.74    spl8_4 <=> r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1))),
% 2.54/0.74    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.54/0.74  fof(f119,plain,(
% 2.54/0.74    r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK0) | r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK1) | ~spl8_4),
% 2.54/0.74    inference(resolution,[],[f96,f43])).
% 2.54/0.74  fof(f96,plain,(
% 2.54/0.74    r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1)) | ~spl8_4),
% 2.54/0.74    inference(avatar_component_clause,[],[f94])).
% 2.54/0.74  fof(f142,plain,(
% 2.54/0.74    spl8_3 | spl8_6),
% 2.54/0.74    inference(avatar_split_clause,[],[f57,f139,f90])).
% 2.54/0.74  fof(f57,plain,(
% 2.54/0.74    r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 2.54/0.74    inference(resolution,[],[f45,f48])).
% 2.54/0.74  fof(f118,plain,(
% 2.54/0.74    ~spl8_3 | spl8_5),
% 2.54/0.74    inference(avatar_split_clause,[],[f56,f116,f90])).
% 2.54/0.74  fof(f56,plain,(
% 2.54/0.74    ( ! [X0] : (~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),X0) | ~r2_hidden(X0,k2_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))) )),
% 2.54/0.74    inference(resolution,[],[f45,f49])).
% 2.54/0.74  fof(f49,plain,(
% 2.54/0.74    ( ! [X0,X3,X1] : (~r2_hidden(sK3(X0,X1),X3) | ~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X1) | sQ7_eqProxy(k3_tarski(X0),X1)) )),
% 2.54/0.74    inference(equality_proxy_replacement,[],[f23,f44])).
% 2.54/0.74  fof(f23,plain,(
% 2.54/0.74    ( ! [X0,X3,X1] : (~r2_hidden(sK3(X0,X1),X3) | ~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 2.54/0.74    inference(cnf_transformation,[],[f6])).
% 2.54/0.74  fof(f97,plain,(
% 2.54/0.74    spl8_3 | spl8_4),
% 2.54/0.74    inference(avatar_split_clause,[],[f58,f94,f90])).
% 2.54/0.74  fof(f58,plain,(
% 2.54/0.74    r2_hidden(sK5(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(sK0,sK1)) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))),
% 2.54/0.74    inference(resolution,[],[f45,f47])).
% 2.54/0.74  fof(f47,plain,(
% 2.54/0.74    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | sQ7_eqProxy(k3_tarski(X0),X1)) )),
% 2.54/0.74    inference(equality_proxy_replacement,[],[f25,f44])).
% 2.54/0.74  fof(f25,plain,(
% 2.54/0.74    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 2.54/0.74    inference(cnf_transformation,[],[f6])).
% 2.54/0.74  % SZS output end Proof for theBenchmark
% 2.54/0.74  % (10042)------------------------------
% 2.54/0.74  % (10042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.74  % (10042)Termination reason: Refutation
% 2.54/0.74  
% 2.54/0.74  % (10042)Memory used [KB]: 7291
% 2.54/0.74  % (10042)Time elapsed: 0.315 s
% 2.54/0.74  % (10042)------------------------------
% 2.54/0.74  % (10042)------------------------------
% 2.54/0.75  % (10027)Success in time 0.37 s
%------------------------------------------------------------------------------
