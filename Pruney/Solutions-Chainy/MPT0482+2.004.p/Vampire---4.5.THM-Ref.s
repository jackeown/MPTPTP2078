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
% DateTime   : Thu Dec  3 12:48:16 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 116 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  163 ( 315 expanded)
%              Number of equality atoms :   12 (  50 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f165,f222,f239])).

fof(f239,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f237,f149])).

fof(f149,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_1
  <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f237,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | ~ spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f236,f176])).

fof(f176,plain,
    ( r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f149,f98])).

fof(f98,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X8),sK1)
      | r2_hidden(X7,sK0) ) ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f18,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

% (6948)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f236,plain,
    ( ~ r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f227,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f227,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | spl8_3 ),
    inference(resolution,[],[f221,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f221,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_3
  <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f222,plain,
    ( ~ spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f66,f151,f219])).

fof(f151,plain,
    ( spl8_2
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f66,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f65,f52])).

fof(f52,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k5_relat_1(k6_relat_1(X7),sK1))
      | r2_hidden(k4_tarski(X5,X6),sK1) ) ),
    inference(resolution,[],[f17,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f60,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f24,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

fof(f39,plain,(
    ~ sQ7_eqProxy(sK1,k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f19,f38])).

fof(f19,plain,(
    sK1 != k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f165,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f163,f17])).

fof(f163,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f158,f20])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f158,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl8_2 ),
    inference(resolution,[],[f153,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f153,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f64,f151,f147])).

fof(f64,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(subsumption_resolution,[],[f63,f52])).

fof(f63,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(subsumption_resolution,[],[f59,f17])).

fof(f59,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | sQ7_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f23,f38])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (6945)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (6939)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (6963)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (6955)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (6947)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (6962)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (6953)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (6954)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (6942)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (6944)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (6961)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (6943)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (6961)Refutation not found, incomplete strategy% (6961)------------------------------
% 0.20/0.53  % (6961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6961)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6961)Memory used [KB]: 10618
% 0.20/0.53  % (6961)Time elapsed: 0.133 s
% 0.20/0.53  % (6961)------------------------------
% 0.20/0.53  % (6961)------------------------------
% 0.20/0.53  % (6946)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (6941)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (6949)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (6964)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (6968)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (6967)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (6966)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (6960)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (6959)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (6941)Refutation not found, incomplete strategy% (6941)------------------------------
% 0.20/0.54  % (6941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6958)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (6952)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (6951)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.54  % (6965)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (6941)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (6941)Memory used [KB]: 10618
% 1.40/0.54  % (6941)Time elapsed: 0.136 s
% 1.40/0.54  % (6941)------------------------------
% 1.40/0.54  % (6941)------------------------------
% 1.40/0.55  % (6957)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (6950)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.56  % (6952)Refutation found. Thanks to Tanya!
% 1.40/0.56  % SZS status Theorem for theBenchmark
% 1.40/0.57  % SZS output start Proof for theBenchmark
% 1.40/0.57  fof(f241,plain,(
% 1.40/0.57    $false),
% 1.40/0.57    inference(avatar_sat_refutation,[],[f154,f165,f222,f239])).
% 1.40/0.57  fof(f239,plain,(
% 1.40/0.57    ~spl8_1 | spl8_3),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f238])).
% 1.40/0.57  fof(f238,plain,(
% 1.40/0.57    $false | (~spl8_1 | spl8_3)),
% 1.40/0.57    inference(subsumption_resolution,[],[f237,f149])).
% 1.40/0.57  fof(f149,plain,(
% 1.40/0.57    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | ~spl8_1),
% 1.40/0.57    inference(avatar_component_clause,[],[f147])).
% 1.40/0.57  fof(f147,plain,(
% 1.40/0.57    spl8_1 <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.40/0.57  fof(f237,plain,(
% 1.40/0.57    ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | (~spl8_1 | spl8_3)),
% 1.40/0.57    inference(subsumption_resolution,[],[f236,f176])).
% 1.40/0.57  fof(f176,plain,(
% 1.40/0.57    r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0) | ~spl8_1),
% 1.40/0.57    inference(resolution,[],[f149,f98])).
% 1.40/0.57  fof(f98,plain,(
% 1.40/0.57    ( ! [X8,X7] : (~r2_hidden(k4_tarski(X7,X8),sK1) | r2_hidden(X7,sK0)) )),
% 1.40/0.57    inference(resolution,[],[f58,f37])).
% 1.40/0.57  fof(f37,plain,(
% 1.40/0.57    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.40/0.57    inference(equality_resolution,[],[f27])).
% 1.40/0.57  fof(f27,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.40/0.57    inference(cnf_transformation,[],[f3])).
% 1.40/0.57  fof(f3,axiom,(
% 1.40/0.57    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.40/0.57  fof(f58,plain,(
% 1.40/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(X0,sK0)) )),
% 1.40/0.57    inference(resolution,[],[f18,f26])).
% 1.40/0.57  fof(f26,plain,(
% 1.40/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 1.40/0.57    inference(cnf_transformation,[],[f15])).
% 1.40/0.57  fof(f15,plain,(
% 1.40/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.40/0.57    inference(ennf_transformation,[],[f9])).
% 1.40/0.57  fof(f9,plain,(
% 1.40/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 1.40/0.57  fof(f1,axiom,(
% 1.40/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.57  fof(f18,plain,(
% 1.40/0.57    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.40/0.57    inference(cnf_transformation,[],[f11])).
% 1.40/0.57  fof(f11,plain,(
% 1.40/0.57    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 1.40/0.57    inference(flattening,[],[f10])).
% 1.40/0.57  fof(f10,plain,(
% 1.40/0.57    ? [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.40/0.57    inference(ennf_transformation,[],[f8])).
% 1.40/0.57  fof(f8,negated_conjecture,(
% 1.40/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.40/0.57    inference(negated_conjecture,[],[f7])).
% 1.40/0.57  % (6948)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.57  fof(f7,conjecture,(
% 1.40/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.40/0.57  fof(f236,plain,(
% 1.40/0.57    ~r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | spl8_3),
% 1.40/0.57    inference(subsumption_resolution,[],[f227,f17])).
% 1.40/0.57  fof(f17,plain,(
% 1.40/0.57    v1_relat_1(sK1)),
% 1.40/0.57    inference(cnf_transformation,[],[f11])).
% 1.40/0.57  fof(f227,plain,(
% 1.40/0.57    ~v1_relat_1(sK1) | ~r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | spl8_3),
% 1.40/0.57    inference(resolution,[],[f221,f33])).
% 1.40/0.57  fof(f33,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f16])).
% 1.40/0.57  fof(f16,plain,(
% 1.40/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 1.40/0.57    inference(ennf_transformation,[],[f6])).
% 1.40/0.57  fof(f6,axiom,(
% 1.40/0.57    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
% 1.40/0.57  fof(f221,plain,(
% 1.40/0.57    ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | spl8_3),
% 1.40/0.57    inference(avatar_component_clause,[],[f219])).
% 1.40/0.57  fof(f219,plain,(
% 1.40/0.57    spl8_3 <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.40/0.57  fof(f222,plain,(
% 1.40/0.57    ~spl8_3 | ~spl8_2),
% 1.40/0.57    inference(avatar_split_clause,[],[f66,f151,f219])).
% 1.40/0.57  fof(f151,plain,(
% 1.40/0.57    spl8_2 <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 1.40/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.40/0.57  fof(f66,plain,(
% 1.40/0.57    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))),
% 1.40/0.57    inference(subsumption_resolution,[],[f65,f52])).
% 1.40/0.57  fof(f52,plain,(
% 1.40/0.57    ( ! [X6,X7,X5] : (~r2_hidden(k4_tarski(X5,X6),k5_relat_1(k6_relat_1(X7),sK1)) | r2_hidden(k4_tarski(X5,X6),sK1)) )),
% 1.40/0.57    inference(resolution,[],[f17,f32])).
% 1.40/0.57  fof(f32,plain,(
% 1.40/0.57    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f16])).
% 1.40/0.57  fof(f65,plain,(
% 1.40/0.57    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 1.40/0.57    inference(subsumption_resolution,[],[f60,f17])).
% 1.40/0.57  fof(f60,plain,(
% 1.40/0.57    ~v1_relat_1(sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 1.40/0.57    inference(resolution,[],[f39,f40])).
% 1.40/0.57  fof(f40,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | sQ7_eqProxy(X0,X1)) )),
% 1.40/0.57    inference(equality_proxy_replacement,[],[f24,f38])).
% 1.40/0.57  fof(f38,plain,(
% 1.40/0.57    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 1.40/0.57    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 1.40/0.57  fof(f24,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | X0 = X1) )),
% 1.40/0.57    inference(cnf_transformation,[],[f12])).
% 1.40/0.57  fof(f12,plain,(
% 1.40/0.57    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.57    inference(ennf_transformation,[],[f2])).
% 1.40/0.57  fof(f2,axiom,(
% 1.40/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).
% 1.40/0.57  fof(f39,plain,(
% 1.40/0.57    ~sQ7_eqProxy(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),
% 1.40/0.57    inference(equality_proxy_replacement,[],[f19,f38])).
% 1.40/0.57  fof(f19,plain,(
% 1.40/0.57    sK1 != k5_relat_1(k6_relat_1(sK0),sK1)),
% 1.40/0.57    inference(cnf_transformation,[],[f11])).
% 1.40/0.57  fof(f165,plain,(
% 1.40/0.57    spl8_2),
% 1.40/0.57    inference(avatar_contradiction_clause,[],[f164])).
% 1.40/0.57  fof(f164,plain,(
% 1.40/0.57    $false | spl8_2),
% 1.40/0.57    inference(subsumption_resolution,[],[f163,f17])).
% 1.40/0.57  fof(f163,plain,(
% 1.40/0.57    ~v1_relat_1(sK1) | spl8_2),
% 1.40/0.57    inference(subsumption_resolution,[],[f158,f20])).
% 1.40/0.57  fof(f20,plain,(
% 1.40/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f5])).
% 1.40/0.57  fof(f5,axiom,(
% 1.40/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.40/0.57  fof(f158,plain,(
% 1.40/0.57    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl8_2),
% 1.40/0.57    inference(resolution,[],[f153,f25])).
% 1.40/0.57  fof(f25,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 1.40/0.57    inference(cnf_transformation,[],[f14])).
% 1.40/0.57  fof(f14,plain,(
% 1.40/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.40/0.57    inference(flattening,[],[f13])).
% 1.40/0.57  fof(f13,plain,(
% 1.40/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.40/0.57    inference(ennf_transformation,[],[f4])).
% 1.40/0.57  fof(f4,axiom,(
% 1.40/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.40/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.40/0.57  fof(f153,plain,(
% 1.40/0.57    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | spl8_2),
% 1.40/0.57    inference(avatar_component_clause,[],[f151])).
% 1.40/0.57  fof(f154,plain,(
% 1.40/0.57    spl8_1 | ~spl8_2),
% 1.40/0.57    inference(avatar_split_clause,[],[f64,f151,f147])).
% 1.40/0.57  fof(f64,plain,(
% 1.40/0.57    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 1.40/0.57    inference(subsumption_resolution,[],[f63,f52])).
% 1.40/0.57  fof(f63,plain,(
% 1.40/0.57    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 1.40/0.57    inference(subsumption_resolution,[],[f59,f17])).
% 1.40/0.57  fof(f59,plain,(
% 1.40/0.57    ~v1_relat_1(sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 1.40/0.57    inference(resolution,[],[f39,f41])).
% 1.40/0.57  fof(f41,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | sQ7_eqProxy(X0,X1)) )),
% 1.40/0.57    inference(equality_proxy_replacement,[],[f23,f38])).
% 1.40/0.57  fof(f23,plain,(
% 1.40/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | X0 = X1) )),
% 1.40/0.57    inference(cnf_transformation,[],[f12])).
% 1.40/0.57  % SZS output end Proof for theBenchmark
% 1.40/0.57  % (6952)------------------------------
% 1.40/0.57  % (6952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (6952)Termination reason: Refutation
% 1.40/0.57  
% 1.40/0.57  % (6952)Memory used [KB]: 6396
% 1.40/0.57  % (6952)Time elapsed: 0.157 s
% 1.40/0.57  % (6952)------------------------------
% 1.40/0.57  % (6952)------------------------------
% 1.64/0.57  % (6938)Success in time 0.211 s
%------------------------------------------------------------------------------
