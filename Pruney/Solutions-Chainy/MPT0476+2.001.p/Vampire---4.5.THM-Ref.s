%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:14 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 114 expanded)
%              Number of leaves         :   14 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  188 ( 305 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1017,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f62,f85,f109,f339,f360,f380,f403,f962,f998,f1016])).

fof(f1016,plain,
    ( ~ spl9_2
    | spl9_3
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_contradiction_clause,[],[f1014])).

fof(f1014,plain,
    ( $false
    | ~ spl9_2
    | spl9_3
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f58,f999])).

fof(f999,plain,
    ( r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_2
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(backward_demodulation,[],[f963,f997])).

fof(f997,plain,
    ( sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f995])).

fof(f995,plain,
    ( spl9_18
  <=> sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f963,plain,
    ( r2_hidden(sK8(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_2
    | ~ spl9_17 ),
    inference(resolution,[],[f961,f410])).

fof(f410,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(sK0))
        | r2_hidden(X0,sK0) )
    | ~ spl9_2 ),
    inference(superposition,[],[f30,f39])).

fof(f39,plain,
    ( sK0 = k1_relat_1(k6_relat_1(sK0))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl9_2
  <=> sK0 = k1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f30,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f961,plain,
    ( r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f959])).

fof(f959,plain,
    ( spl9_17
  <=> r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f58,plain,
    ( ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl9_3
  <=> r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f998,plain,
    ( spl9_18
    | ~ spl9_6
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f965,f959,f73,f995])).

fof(f73,plain,
    ( spl9_6
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f965,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0)
    | ~ spl9_17 ),
    inference(resolution,[],[f961,f27])).

fof(f27,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | X2 = X3
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f962,plain,
    ( spl9_1
    | spl9_17
    | spl9_3 ),
    inference(avatar_split_clause,[],[f112,f56,f959,f34])).

fof(f34,plain,
    ( spl9_1
  <=> sK0 = k2_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f112,plain,
    ( r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | sK0 = k2_relat_1(k6_relat_1(sK0))
    | spl9_3 ),
    inference(resolution,[],[f58,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f403,plain,
    ( ~ spl9_10
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f362,f337,f73,f333])).

fof(f333,plain,
    ( spl9_10
  <=> r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f337,plain,
    ( spl9_11
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f362,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_11 ),
    inference(resolution,[],[f338,f26])).

fof(f26,plain,(
    ! [X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(k4_tarski(X3,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | X2 != X3
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f338,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f337])).

fof(f380,plain,
    ( spl9_2
    | spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f365,f337,f333,f38])).

fof(f365,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)
    | sK0 = k1_relat_1(k6_relat_1(sK0))
    | ~ spl9_11 ),
    inference(resolution,[],[f338,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f360,plain,
    ( spl9_11
    | ~ spl9_6
    | spl9_10 ),
    inference(avatar_split_clause,[],[f341,f333,f73,f337])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0)) )
    | spl9_10 ),
    inference(resolution,[],[f335,f28])).

fof(f28,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f335,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f333])).

fof(f339,plain,
    ( ~ spl9_10
    | spl9_11
    | spl9_2 ),
    inference(avatar_split_clause,[],[f77,f38,f337,f333])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))
        | ~ r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0) )
    | spl9_2 ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,
    ( ! [X2,X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),X1),X2),k6_relat_1(sK0))
        | ~ r2_hidden(sK3(k6_relat_1(sK0),X1),X1) )
    | spl9_2 ),
    inference(superposition,[],[f40,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f40,plain,
    ( sK0 != k1_relat_1(k6_relat_1(sK0))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f109,plain,
    ( ~ spl9_3
    | ~ spl9_6
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f93,f60,f73,f56])).

fof(f60,plain,
    ( spl9_4
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f93,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f61,f26])).

fof(f61,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f85,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl9_6 ),
    inference(resolution,[],[f75,f10])).

fof(f10,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f75,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f62,plain,
    ( ~ spl9_3
    | spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f54,f34,f60,f56])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))
        | ~ r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) )
    | spl9_1 ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,
    ( ! [X2,X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(X2,sK6(k6_relat_1(sK0),X1)),k6_relat_1(sK0))
        | ~ r2_hidden(sK6(k6_relat_1(sK0),X1),X1) )
    | spl9_1 ),
    inference(superposition,[],[f36,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,
    ( sK0 != k2_relat_1(k6_relat_1(sK0))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f41,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f9,f38,f34])).

fof(f9,plain,
    ( sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK0 != k2_relat_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k2_relat_1(k6_relat_1(X0)) != X0
      | k1_relat_1(k6_relat_1(X0)) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( k2_relat_1(k6_relat_1(X0)) = X0
        & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:47:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (2746)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (2754)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (2746)Refutation not found, incomplete strategy% (2746)------------------------------
% 0.21/0.49  % (2746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2746)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2746)Memory used [KB]: 1663
% 0.21/0.49  % (2746)Time elapsed: 0.071 s
% 0.21/0.49  % (2746)------------------------------
% 0.21/0.49  % (2746)------------------------------
% 0.21/0.52  % (2745)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (2741)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (2745)Refutation not found, incomplete strategy% (2745)------------------------------
% 0.21/0.52  % (2745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2745)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2745)Memory used [KB]: 10618
% 0.21/0.52  % (2745)Time elapsed: 0.040 s
% 0.21/0.52  % (2745)------------------------------
% 0.21/0.52  % (2745)------------------------------
% 0.21/0.53  % (2753)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (2742)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (2743)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (2744)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (2751)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (2749)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (2759)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  % (2740)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (2761)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (2740)Refutation not found, incomplete strategy% (2740)------------------------------
% 0.21/0.55  % (2740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2740)Memory used [KB]: 10618
% 0.21/0.55  % (2740)Time elapsed: 0.136 s
% 0.21/0.55  % (2740)------------------------------
% 0.21/0.55  % (2740)------------------------------
% 0.21/0.55  % (2757)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (2760)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (2739)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (2744)Refutation not found, incomplete strategy% (2744)------------------------------
% 0.21/0.55  % (2744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (2744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (2744)Memory used [KB]: 6012
% 0.21/0.55  % (2744)Time elapsed: 0.123 s
% 0.21/0.55  % (2744)------------------------------
% 0.21/0.55  % (2744)------------------------------
% 0.21/0.56  % (2739)Refutation not found, incomplete strategy% (2739)------------------------------
% 0.21/0.56  % (2739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2739)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2739)Memory used [KB]: 10618
% 0.21/0.56  % (2739)Time elapsed: 0.116 s
% 0.21/0.56  % (2739)------------------------------
% 0.21/0.56  % (2739)------------------------------
% 0.21/0.56  % (2748)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (2764)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (2752)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (2752)Refutation not found, incomplete strategy% (2752)------------------------------
% 0.21/0.56  % (2752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (2752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (2752)Memory used [KB]: 6140
% 0.21/0.56  % (2752)Time elapsed: 0.133 s
% 0.21/0.56  % (2752)------------------------------
% 0.21/0.56  % (2752)------------------------------
% 0.21/0.56  % (2758)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (2755)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.56  % (2750)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.57  % (2762)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (2763)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.57  % (2756)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.58  % (2747)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.74/0.60  % (2759)Refutation found. Thanks to Tanya!
% 1.74/0.60  % SZS status Theorem for theBenchmark
% 1.74/0.60  % SZS output start Proof for theBenchmark
% 1.74/0.60  fof(f1017,plain,(
% 1.74/0.60    $false),
% 1.74/0.60    inference(avatar_sat_refutation,[],[f41,f62,f85,f109,f339,f360,f380,f403,f962,f998,f1016])).
% 1.74/0.60  fof(f1016,plain,(
% 1.74/0.60    ~spl9_2 | spl9_3 | ~spl9_17 | ~spl9_18),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1014])).
% 1.74/0.60  fof(f1014,plain,(
% 1.74/0.60    $false | (~spl9_2 | spl9_3 | ~spl9_17 | ~spl9_18)),
% 1.74/0.60    inference(subsumption_resolution,[],[f58,f999])).
% 1.74/0.60  fof(f999,plain,(
% 1.74/0.60    r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) | (~spl9_2 | ~spl9_17 | ~spl9_18)),
% 1.74/0.60    inference(backward_demodulation,[],[f963,f997])).
% 1.74/0.60  fof(f997,plain,(
% 1.74/0.60    sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0) | ~spl9_18),
% 1.74/0.60    inference(avatar_component_clause,[],[f995])).
% 1.74/0.60  fof(f995,plain,(
% 1.74/0.60    spl9_18 <=> sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.74/0.60  fof(f963,plain,(
% 1.74/0.60    r2_hidden(sK8(k6_relat_1(sK0),sK0),sK0) | (~spl9_2 | ~spl9_17)),
% 1.74/0.60    inference(resolution,[],[f961,f410])).
% 1.74/0.60  fof(f410,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k6_relat_1(sK0)) | r2_hidden(X0,sK0)) ) | ~spl9_2),
% 1.74/0.60    inference(superposition,[],[f30,f39])).
% 1.74/0.60  fof(f39,plain,(
% 1.74/0.60    sK0 = k1_relat_1(k6_relat_1(sK0)) | ~spl9_2),
% 1.74/0.60    inference(avatar_component_clause,[],[f38])).
% 1.74/0.60  fof(f38,plain,(
% 1.74/0.60    spl9_2 <=> sK0 = k1_relat_1(k6_relat_1(sK0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.74/0.60  fof(f30,plain,(
% 1.74/0.60    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.74/0.60    inference(equality_resolution,[],[f17])).
% 1.74/0.60  fof(f17,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f2])).
% 1.74/0.60  fof(f2,axiom,(
% 1.74/0.60    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.74/0.60  fof(f961,plain,(
% 1.74/0.60    r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) | ~spl9_17),
% 1.74/0.60    inference(avatar_component_clause,[],[f959])).
% 1.74/0.60  fof(f959,plain,(
% 1.74/0.60    spl9_17 <=> r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    ~r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) | spl9_3),
% 1.74/0.60    inference(avatar_component_clause,[],[f56])).
% 1.74/0.60  fof(f56,plain,(
% 1.74/0.60    spl9_3 <=> r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.74/0.60  fof(f998,plain,(
% 1.74/0.60    spl9_18 | ~spl9_6 | ~spl9_17),
% 1.74/0.60    inference(avatar_split_clause,[],[f965,f959,f73,f995])).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    spl9_6 <=> v1_relat_1(k6_relat_1(sK0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.74/0.60  fof(f965,plain,(
% 1.74/0.60    ~v1_relat_1(k6_relat_1(sK0)) | sK6(k6_relat_1(sK0),sK0) = sK8(k6_relat_1(sK0),sK0) | ~spl9_17),
% 1.74/0.60    inference(resolution,[],[f961,f27])).
% 1.74/0.60  fof(f27,plain,(
% 1.74/0.60    ( ! [X2,X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | X2 = X3 | ~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))) )),
% 1.74/0.60    inference(equality_resolution,[],[f15])).
% 1.74/0.60  fof(f15,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | X2 = X3 | ~r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f8])).
% 1.74/0.60  fof(f8,plain,(
% 1.74/0.60    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 1.74/0.60    inference(ennf_transformation,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).
% 1.74/0.60  fof(f962,plain,(
% 1.74/0.60    spl9_1 | spl9_17 | spl9_3),
% 1.74/0.60    inference(avatar_split_clause,[],[f112,f56,f959,f34])).
% 1.74/0.60  fof(f34,plain,(
% 1.74/0.60    spl9_1 <=> sK0 = k2_relat_1(k6_relat_1(sK0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.74/0.60  fof(f112,plain,(
% 1.74/0.60    r2_hidden(k4_tarski(sK8(k6_relat_1(sK0),sK0),sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) | sK0 = k2_relat_1(k6_relat_1(sK0)) | spl9_3),
% 1.74/0.60    inference(resolution,[],[f58,f23])).
% 1.74/0.60  fof(f23,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f3])).
% 1.74/0.60  fof(f3,axiom,(
% 1.74/0.60    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.74/0.60  fof(f403,plain,(
% 1.74/0.60    ~spl9_10 | ~spl9_6 | ~spl9_11),
% 1.74/0.60    inference(avatar_split_clause,[],[f362,f337,f73,f333])).
% 1.74/0.60  fof(f333,plain,(
% 1.74/0.60    spl9_10 <=> r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.74/0.60  fof(f337,plain,(
% 1.74/0.60    spl9_11 <=> ! [X0] : ~r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.74/0.60  fof(f362,plain,(
% 1.74/0.60    ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0) | ~spl9_11),
% 1.74/0.60    inference(resolution,[],[f338,f26])).
% 1.74/0.60  fof(f26,plain,(
% 1.74/0.60    ( ! [X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),k6_relat_1(X0))) )),
% 1.74/0.60    inference(equality_resolution,[],[f25])).
% 1.74/0.60  fof(f25,plain,(
% 1.74/0.60    ( ! [X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X3,X0) | r2_hidden(k4_tarski(X3,X3),X1) | k6_relat_1(X0) != X1) )),
% 1.74/0.60    inference(equality_resolution,[],[f16])).
% 1.74/0.60  fof(f16,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | X2 != X3 | r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f8])).
% 1.74/0.60  fof(f338,plain,(
% 1.74/0.60    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))) ) | ~spl9_11),
% 1.74/0.60    inference(avatar_component_clause,[],[f337])).
% 1.74/0.60  fof(f380,plain,(
% 1.74/0.60    spl9_2 | spl9_10 | ~spl9_11),
% 1.74/0.60    inference(avatar_split_clause,[],[f365,f337,f333,f38])).
% 1.74/0.60  fof(f365,plain,(
% 1.74/0.60    r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0) | sK0 = k1_relat_1(k6_relat_1(sK0)) | ~spl9_11),
% 1.74/0.60    inference(resolution,[],[f338,f19])).
% 1.74/0.60  fof(f19,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f2])).
% 1.74/0.60  fof(f360,plain,(
% 1.74/0.60    spl9_11 | ~spl9_6 | spl9_10),
% 1.74/0.60    inference(avatar_split_clause,[],[f341,f333,f73,f337])).
% 1.74/0.60  fof(f341,plain,(
% 1.74/0.60    ( ! [X0] : (~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0))) ) | spl9_10),
% 1.74/0.60    inference(resolution,[],[f335,f28])).
% 1.74/0.60  fof(f28,plain,(
% 1.74/0.60    ( ! [X2,X0,X3] : (~v1_relat_1(k6_relat_1(X0)) | r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))) )),
% 1.74/0.60    inference(equality_resolution,[],[f14])).
% 1.74/0.60  fof(f14,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | k6_relat_1(X0) != X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f8])).
% 1.74/0.60  fof(f335,plain,(
% 1.74/0.60    ~r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0) | spl9_10),
% 1.74/0.60    inference(avatar_component_clause,[],[f333])).
% 1.74/0.60  fof(f339,plain,(
% 1.74/0.60    ~spl9_10 | spl9_11 | spl9_2),
% 1.74/0.60    inference(avatar_split_clause,[],[f77,f38,f337,f333])).
% 1.74/0.60  fof(f77,plain,(
% 1.74/0.60    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),sK0),X0),k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK0),sK0)) ) | spl9_2),
% 1.74/0.60    inference(equality_resolution,[],[f52])).
% 1.74/0.60  fof(f52,plain,(
% 1.74/0.60    ( ! [X2,X1] : (sK0 != X1 | ~r2_hidden(k4_tarski(sK3(k6_relat_1(sK0),X1),X2),k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),X1),X1)) ) | spl9_2),
% 1.74/0.60    inference(superposition,[],[f40,f20])).
% 1.74/0.60  fof(f20,plain,(
% 1.74/0.60    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f2])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    sK0 != k1_relat_1(k6_relat_1(sK0)) | spl9_2),
% 1.74/0.60    inference(avatar_component_clause,[],[f38])).
% 1.74/0.60  fof(f109,plain,(
% 1.74/0.60    ~spl9_3 | ~spl9_6 | ~spl9_4),
% 1.74/0.60    inference(avatar_split_clause,[],[f93,f60,f73,f56])).
% 1.74/0.60  fof(f60,plain,(
% 1.74/0.60    spl9_4 <=> ! [X0] : ~r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.74/0.60  fof(f93,plain,(
% 1.74/0.60    ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0) | ~spl9_4),
% 1.74/0.60    inference(resolution,[],[f61,f26])).
% 1.74/0.60  fof(f61,plain,(
% 1.74/0.60    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0))) ) | ~spl9_4),
% 1.74/0.60    inference(avatar_component_clause,[],[f60])).
% 1.74/0.60  fof(f85,plain,(
% 1.74/0.60    spl9_6),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f78])).
% 1.74/0.60  fof(f78,plain,(
% 1.74/0.60    $false | spl9_6),
% 1.74/0.60    inference(resolution,[],[f75,f10])).
% 1.74/0.60  fof(f10,plain,(
% 1.74/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f4])).
% 1.74/0.60  fof(f4,axiom,(
% 1.74/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.74/0.60  fof(f75,plain,(
% 1.74/0.60    ~v1_relat_1(k6_relat_1(sK0)) | spl9_6),
% 1.74/0.60    inference(avatar_component_clause,[],[f73])).
% 1.74/0.60  fof(f62,plain,(
% 1.74/0.60    ~spl9_3 | spl9_4 | spl9_1),
% 1.74/0.60    inference(avatar_split_clause,[],[f54,f34,f60,f56])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(k6_relat_1(sK0),sK0)),k6_relat_1(sK0)) | ~r2_hidden(sK6(k6_relat_1(sK0),sK0),sK0)) ) | spl9_1),
% 1.74/0.60    inference(equality_resolution,[],[f46])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    ( ! [X2,X1] : (sK0 != X1 | ~r2_hidden(k4_tarski(X2,sK6(k6_relat_1(sK0),X1)),k6_relat_1(sK0)) | ~r2_hidden(sK6(k6_relat_1(sK0),X1),X1)) ) | spl9_1),
% 1.74/0.60    inference(superposition,[],[f36,f24])).
% 1.74/0.60  fof(f24,plain,(
% 1.74/0.60    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0) | ~r2_hidden(sK6(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f3])).
% 1.74/0.60  fof(f36,plain,(
% 1.74/0.60    sK0 != k2_relat_1(k6_relat_1(sK0)) | spl9_1),
% 1.74/0.60    inference(avatar_component_clause,[],[f34])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ~spl9_1 | ~spl9_2),
% 1.74/0.60    inference(avatar_split_clause,[],[f9,f38,f34])).
% 1.74/0.60  fof(f9,plain,(
% 1.74/0.60    sK0 != k1_relat_1(k6_relat_1(sK0)) | sK0 != k2_relat_1(k6_relat_1(sK0))),
% 1.74/0.60    inference(cnf_transformation,[],[f7])).
% 1.74/0.60  fof(f7,plain,(
% 1.74/0.60    ? [X0] : (k2_relat_1(k6_relat_1(X0)) != X0 | k1_relat_1(k6_relat_1(X0)) != X0)),
% 1.74/0.60    inference(ennf_transformation,[],[f6])).
% 1.74/0.60  fof(f6,negated_conjecture,(
% 1.74/0.60    ~! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.74/0.60    inference(negated_conjecture,[],[f5])).
% 1.74/0.60  fof(f5,conjecture,(
% 1.74/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.74/0.60  % SZS output end Proof for theBenchmark
% 1.74/0.60  % (2759)------------------------------
% 1.74/0.60  % (2759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.60  % (2759)Termination reason: Refutation
% 1.74/0.60  
% 1.74/0.60  % (2759)Memory used [KB]: 11129
% 1.74/0.60  % (2759)Time elapsed: 0.176 s
% 1.74/0.60  % (2759)------------------------------
% 1.74/0.60  % (2759)------------------------------
% 1.74/0.60  % (2738)Success in time 0.242 s
%------------------------------------------------------------------------------
