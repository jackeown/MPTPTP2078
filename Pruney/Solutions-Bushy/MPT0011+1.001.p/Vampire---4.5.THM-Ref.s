%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0011+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 198 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 (1189 expanded)
%              Number of equality atoms :   23 ( 157 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f47,f48,f64,f70,f79,f85,f95,f102,f108,f109])).

fof(f109,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f76,f35,f43])).

fof(f43,plain,
    ( spl5_3
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f35,plain,
    ( spl5_1
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

% (10808)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (10808)Refutation not found, incomplete strategy% (10808)------------------------------
% (10808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10808)Termination reason: Refutation not found, incomplete strategy

% (10808)Memory used [KB]: 10490
% (10808)Time elapsed: 0.089 s
% (10808)------------------------------
% (10808)------------------------------
% (10801)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (10807)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (10798)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (10786)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (10798)Refutation not found, incomplete strategy% (10798)------------------------------
% (10798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10798)Termination reason: Refutation not found, incomplete strategy

% (10798)Memory used [KB]: 10618
% (10798)Time elapsed: 0.087 s
% (10798)------------------------------
% (10798)------------------------------
% (10786)Refutation not found, incomplete strategy% (10786)------------------------------
% (10786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10786)Termination reason: Refutation not found, incomplete strategy

% (10786)Memory used [KB]: 6012
% (10786)Time elapsed: 0.085 s
% (10786)------------------------------
% (10786)------------------------------
% (10789)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f76,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | spl5_1 ),
    inference(resolution,[],[f67,f21])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f67,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | spl5_1 ),
    inference(resolution,[],[f36,f21])).

fof(f36,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f108,plain,
    ( spl5_5
    | spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f98,f92,f43,f61])).

fof(f61,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f92,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f98,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f94,f23])).

fof(f23,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f102,plain,
    ( ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f81,f39,f57])).

fof(f57,plain,
    ( spl5_4
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f39,plain,
    ( spl5_2
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl5_2 ),
    inference(resolution,[],[f40,f22])).

fof(f22,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f95,plain,
    ( spl5_4
    | spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f88,f35,f92,f57])).

fof(f88,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f37,f23])).

fof(f37,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f85,plain,
    ( ~ spl5_5
    | spl5_2 ),
    inference(avatar_split_clause,[],[f82,f39,f61])).

fof(f82,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | spl5_2 ),
    inference(resolution,[],[f40,f21])).

fof(f79,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f75,f35,f61])).

fof(f75,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | spl5_1 ),
    inference(resolution,[],[f67,f22])).

fof(f70,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f66,f35,f57])).

fof(f66,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl5_1 ),
    inference(resolution,[],[f36,f22])).

% (10792)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f64,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f53,f39,f61,f57])).

fof(f53,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f41,f23])).

fof(f41,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

% (10800)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f48,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f33,f43,f35])).

fof(f33,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f25,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f20,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ~ sQ4_eqProxy(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f13,f24])).

fof(f13,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2))
   => k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f47,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f32,f39,f35])).

fof(f32,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f25,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f19,f24])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,
    ( spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f31,f43,f39,f35])).

fof(f31,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f18,f24])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
