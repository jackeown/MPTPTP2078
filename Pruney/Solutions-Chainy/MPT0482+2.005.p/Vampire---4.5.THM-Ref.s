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
% DateTime   : Thu Dec  3 12:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 123 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 338 expanded)
%              Number of equality atoms :   10 (  52 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f173,f227,f244])).

fof(f244,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f242,f157])).

fof(f157,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f242,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f241,f186])).

fof(f186,plain,
    ( r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f157,f101])).

fof(f101,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f98,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
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

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f98,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,sK0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X5,X6),sK1) ) ),
    inference(resolution,[],[f56,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f20,f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f20,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f241,plain,
    ( ~ r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f232,f19])).

fof(f232,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)
    | spl5_3 ),
    inference(resolution,[],[f226,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(f226,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl5_3
  <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f227,plain,
    ( ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f64,f159,f224])).

fof(f159,plain,
    ( spl5_2
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f64,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f63,f50])).

fof(f50,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X10),k5_relat_1(k6_relat_1(X11),sK1))
      | r2_hidden(k4_tarski(X9,X10),sK1) ) ),
    inference(resolution,[],[f19,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(subsumption_resolution,[],[f58,f19])).

fof(f58,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(resolution,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f26,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(f37,plain,(
    ~ sQ4_eqProxy(sK1,k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f21,f36])).

fof(f21,plain,(
    sK1 != k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f173,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f171,f19])).

fof(f171,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f166,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f166,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl5_2 ),
    inference(resolution,[],[f161,f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f161,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f62,f159,f155])).

fof(f62,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(subsumption_resolution,[],[f61,f50])).

fof(f61,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(subsumption_resolution,[],[f57,f19])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))
    | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f25,f36])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (19332)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.49  % (19321)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (19313)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (19333)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (19324)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.50  % (19316)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (19322)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (19314)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (19311)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (19315)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (19308)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (19332)Refutation not found, incomplete strategy% (19332)------------------------------
% 0.22/0.51  % (19332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19332)Memory used [KB]: 10618
% 0.22/0.51  % (19332)Time elapsed: 0.101 s
% 0.22/0.51  % (19332)------------------------------
% 0.22/0.51  % (19332)------------------------------
% 0.22/0.51  % (19312)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (19329)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (19328)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (19330)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (19310)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (19331)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (19319)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (19334)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (19311)Refutation not found, incomplete strategy% (19311)------------------------------
% 0.22/0.53  % (19311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19311)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19311)Memory used [KB]: 10618
% 0.22/0.53  % (19311)Time elapsed: 0.117 s
% 0.22/0.53  % (19311)------------------------------
% 0.22/0.53  % (19311)------------------------------
% 0.22/0.53  % (19323)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (19320)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (19336)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (19322)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f246,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f162,f173,f227,f244])).
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    ~spl5_1 | spl5_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f243])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    $false | (~spl5_1 | spl5_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f242,f157])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f155])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    spl5_1 <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | (~spl5_1 | spl5_3)),
% 0.22/0.54    inference(subsumption_resolution,[],[f241,f186])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0) | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f157,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X6,X5] : (~r2_hidden(k4_tarski(X5,X6),sK1) | r2_hidden(X5,sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f98,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    v1_relat_1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f7])).
% 0.22/0.54  fof(f7,conjecture,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X6,X5] : (r2_hidden(X5,sK0) | ~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X5,X6),sK1)) )),
% 0.22/0.54    inference(resolution,[],[f56,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(X0,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f20,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    ~r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | spl5_3),
% 0.22/0.54    inference(subsumption_resolution,[],[f232,f19])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    ~v1_relat_1(sK1) | ~r2_hidden(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK0) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1) | spl5_3),
% 0.22/0.54    inference(resolution,[],[f226,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f224])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    spl5_3 <=> r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    ~spl5_3 | ~spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f64,f159,f224])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    spl5_2 <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f63,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X10,X11,X9] : (~r2_hidden(k4_tarski(X9,X10),k5_relat_1(k6_relat_1(X11),sK1)) | r2_hidden(k4_tarski(X9,X10),sK1)) )),
% 0.22/0.54    inference(resolution,[],[f19,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f58,f19])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ~v1_relat_1(sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | ~r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 0.22/0.54    inference(resolution,[],[f37,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | sQ4_eqProxy(X0,X1)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f26,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ~sQ4_eqProxy(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f21,f36])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    sK1 != k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    spl5_2),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f172])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    $false | spl5_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f171,f19])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ~v1_relat_1(sK1) | spl5_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f166,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl5_2),
% 0.22/0.54    inference(resolution,[],[f161,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f159])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    spl5_1 | ~spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f62,f159,f155])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f61,f50])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 0.22/0.54    inference(subsumption_resolution,[],[f57,f19])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~v1_relat_1(sK1) | ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),k5_relat_1(k6_relat_1(sK0),sK1)) | r2_hidden(k4_tarski(sK2(sK1,k5_relat_1(k6_relat_1(sK0),sK1)),sK3(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),sK1)),
% 0.22/0.54    inference(resolution,[],[f37,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | sQ4_eqProxy(X0,X1)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f25,f36])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | X0 = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (19322)------------------------------
% 0.22/0.54  % (19322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19322)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (19322)Memory used [KB]: 6396
% 0.22/0.54  % (19322)Time elapsed: 0.120 s
% 0.22/0.54  % (19322)------------------------------
% 0.22/0.54  % (19322)------------------------------
% 0.22/0.54  % (19305)Success in time 0.179 s
%------------------------------------------------------------------------------
