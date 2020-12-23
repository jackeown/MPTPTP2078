%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0938+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:56 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 229 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   24
%              Number of atoms          :  406 (1493 expanded)
%              Number of equality atoms :   28 ( 121 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f101,f103,f113,f115,f133,f136,f139])).

fof(f139,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f137,f96,f55])).

fof(f55,plain,
    ( spl6_1
  <=> v8_relat_2(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f96,plain,
    ( spl6_3
  <=> r8_relat_2(k1_wellord2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f137,plain,
    ( v8_relat_2(k1_wellord2(sK0))
    | ~ spl6_3 ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r8_relat_2(k1_wellord2(X0),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(global_subsumption,[],[f29,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r8_relat_2(k1_wellord2(X0),X0)
      | v8_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f31,f60])).

fof(f60,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f29,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r8_relat_2(X0,k3_relat_1(X0))
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f97,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f136,plain,
    ( ~ spl6_2
    | spl6_3
    | spl6_7 ),
    inference(avatar_split_clause,[],[f135,f131,f96,f93])).

fof(f93,plain,
    ( spl6_2
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f131,plain,
    ( spl6_7
  <=> r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f135,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl6_7 ),
    inference(resolution,[],[f132,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

% (3921)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (3930)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (3927)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (3927)Refutation not found, incomplete strategy% (3927)------------------------------
% (3927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3927)Termination reason: Refutation not found, incomplete strategy

% (3927)Memory used [KB]: 10618
% (3927)Time elapsed: 0.079 s
% (3927)------------------------------
% (3927)------------------------------
% (3934)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (3933)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (3925)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (3936)Refutation not found, incomplete strategy% (3936)------------------------------
% (3936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3936)Termination reason: Refutation not found, incomplete strategy

% (3936)Memory used [KB]: 10490
% (3936)Time elapsed: 0.081 s
% (3936)------------------------------
% (3936)------------------------------
% (3919)Refutation not found, incomplete strategy% (3919)------------------------------
% (3919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3919)Termination reason: Refutation not found, incomplete strategy

% (3919)Memory used [KB]: 10618
% (3919)Time elapsed: 0.080 s
% (3919)------------------------------
% (3919)------------------------------
% (3931)Refutation not found, incomplete strategy% (3931)------------------------------
% (3931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3931)Termination reason: Refutation not found, incomplete strategy

% (3931)Memory used [KB]: 6140
% (3931)Time elapsed: 0.066 s
% (3931)------------------------------
% (3931)------------------------------
% (3918)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(f132,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | spl6_6 ),
    inference(avatar_split_clause,[],[f129,f111,f131,f108,f96,f93])).

fof(f108,plain,
    ( spl6_5
  <=> r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f111,plain,
    ( spl6_6
  <=> r1_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f129,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(sK0))
    | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl6_6 ),
    inference(resolution,[],[f116,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k1_wellord2(sK0),sK0),X0)
        | ~ r2_hidden(k4_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0)),k1_wellord2(X0))
        | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),X0) )
    | spl6_6 ),
    inference(resolution,[],[f112,f59])).

fof(f59,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(global_subsumption,[],[f29,f52])).

fof(f52,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,
    ( ~ r1_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f115,plain,
    ( ~ spl6_2
    | spl6_3
    | spl6_5 ),
    inference(avatar_split_clause,[],[f114,f108,f96,f93])).

fof(f114,plain,
    ( r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl6_5 ),
    inference(resolution,[],[f109,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f113,plain,
    ( ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f105,f99,f111,f108,f96,f93])).

fof(f99,plain,
    ( spl6_4
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f105,plain,
    ( ~ r1_tarski(sK2(k1_wellord2(sK0),sK0),sK3(k1_wellord2(sK0),sK0))
    | ~ r2_hidden(sK2(k1_wellord2(sK0),sK0),sK0)
    | r8_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl6_4 ),
    inference(resolution,[],[f100,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f103,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f94,f29])).

fof(f94,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f101,plain,
    ( ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f91,f55,f99,f96,f93])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(sK0))
        | ~ r2_hidden(X0,sK0)
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0))
        | r8_relat_2(k1_wellord2(sK0),sK0)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | spl6_1 ),
    inference(resolution,[],[f80,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1(k1_wellord2(sK0),sK0),X1)
        | ~ r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),sK0),X0),k1_wellord2(X1))
        | ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) )
    | spl6_1 ),
    inference(resolution,[],[f76,f59])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1(k1_wellord2(sK0),sK0),X0)
        | ~ r1_tarski(X0,sK3(k1_wellord2(sK0),sK0)) )
    | spl6_1 ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,
    ( ~ v8_relat_2(k1_wellord2(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f75,plain,(
    ! [X2,X3] :
      ( v8_relat_2(k1_wellord2(X2))
      | ~ r1_tarski(X3,sK3(k1_wellord2(X2),X2))
      | ~ r1_tarski(sK1(k1_wellord2(X2),X2),X3) ) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X0),sK3(k1_wellord2(X0),X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f72,f62])).

fof(f72,plain,(
    ! [X0] :
      ( r8_relat_2(k1_wellord2(X0),X0)
      | ~ r1_tarski(sK1(k1_wellord2(X0),X0),sK3(k1_wellord2(X0),X0)) ) ),
    inference(global_subsumption,[],[f29,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X0),sK3(k1_wellord2(X0),X0))
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f70])).

% (3935)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X0),sK3(k1_wellord2(X0),X0))
      | r8_relat_2(k1_wellord2(X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f69,f33])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | ~ r1_tarski(sK1(k1_wellord2(X0),X0),sK3(k1_wellord2(X0),X0))
      | r8_relat_2(k1_wellord2(X0),X0) ) ),
    inference(global_subsumption,[],[f29,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X0),sK3(k1_wellord2(X0),X0))
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X0),sK3(k1_wellord2(X0),X0))
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k1_wellord2(X0),X1),X0)
      | ~ r1_tarski(sK1(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r8_relat_2(k1_wellord2(X0),X1) ) ),
    inference(global_subsumption,[],[f29,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK3(k1_wellord2(X0),X1),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r8_relat_2(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(global_subsumption,[],[f29,f51])).

fof(f51,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f16])).

fof(f16,plain,
    ( ? [X0] : ~ v8_relat_2(k1_wellord2(X0))
   => ~ v8_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

%------------------------------------------------------------------------------
