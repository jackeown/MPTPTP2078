%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 232 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  399 (1031 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f64,f84,f87,f94,f98,f110,f128,f135,f146,f163,f178,f230,f253])).

fof(f253,plain,
    ( ~ spl8_6
    | spl8_1
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f250,f228,f46,f79])).

fof(f79,plain,
    ( spl8_6
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f46,plain,
    ( spl8_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f228,plain,
    ( spl8_33
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f250,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl8_33 ),
    inference(resolution,[],[f229,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (27303)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (27312)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (27305)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (27313)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (27317)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (27319)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (27310)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (27300)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (27311)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (27304)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f229,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl8_33
    | ~ spl8_18
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f220,f176,f144,f228])).

fof(f144,plain,
    ( spl8_18
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,X0))
        | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f176,plain,
    ( spl8_24
  <=> r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f220,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1))
    | ~ spl8_18
    | ~ spl8_24 ),
    inference(resolution,[],[f145,f177])).

fof(f177,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f176])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0)
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,X0)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f178,plain,
    ( ~ spl8_5
    | spl8_24
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f172,f161,f176,f62])).

fof(f62,plain,
    ( spl8_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f161,plain,
    ( spl8_21
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f172,plain,
    ( r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl8_21 ),
    inference(resolution,[],[f162,f65])).

fof(f65,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (27320)Refutation not found, incomplete strategy% (27320)------------------------------
% (27320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27320)Termination reason: Refutation not found, incomplete strategy

% (27320)Memory used [KB]: 10490
% (27320)Time elapsed: 0.106 s
% (27320)------------------------------
% (27320)------------------------------
fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK6(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
                    & r2_hidden(sK6(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f162,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK1))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl8_21
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f157,f92,f50,f161])).

fof(f50,plain,
    ( spl8_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f92,plain,
    ( spl8_8
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,X0))
        | ~ r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f157,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK1))
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(resolution,[],[f93,f51])).

fof(f51,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,X0)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f146,plain,
    ( ~ spl8_4
    | spl8_18
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f140,f133,f144,f58])).

fof(f58,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f133,plain,
    ( spl8_16
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f140,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,X0))
        | ~ r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_16 ),
    inference(resolution,[],[f134,f67])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f42,f40])).

fof(f42,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f134,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl8_16
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f129,f126,f54,f133])).

fof(f54,plain,
    ( spl8_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f126,plain,
    ( spl8_15
  <=> ! [X1] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X1)
        | ~ r1_tarski(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f129,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)
    | ~ spl8_3
    | ~ spl8_15 ),
    inference(resolution,[],[f127,f55])).

fof(f55,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f127,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X1) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( ~ spl8_5
    | spl8_15
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f120,f108,f126,f62])).

fof(f108,plain,
    ( spl8_11
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f120,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X1)
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_11 ),
    inference(resolution,[],[f109,f31])).

fof(f31,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f110,plain,
    ( ~ spl8_5
    | spl8_11
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f103,f96,f108,f62])).

fof(f96,plain,
    ( spl8_9
  <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(resolution,[],[f97,f66])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( ~ spl8_6
    | spl8_9
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f89,f82,f96,f79])).

fof(f82,plain,
    ( spl8_7
  <=> ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f89,plain,
    ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl8_7 ),
    inference(resolution,[],[f83,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X0) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f94,plain,
    ( ~ spl8_5
    | spl8_8
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f88,f82,f92,f62])).

fof(f88,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,X0))
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_7 ),
    inference(resolution,[],[f83,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f87,plain,
    ( ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f85,f79,f62])).

fof(f85,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_6 ),
    inference(resolution,[],[f80,f40])).

fof(f80,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f84,plain,
    ( ~ spl8_6
    | spl8_7
    | spl8_1 ),
    inference(avatar_split_clause,[],[f77,f46,f82,f79])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X0)
        | ~ v1_relat_1(k7_relat_1(sK2,sK0))
        | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X0) )
    | spl8_1 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)
      | ~ r1_tarski(X0,X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f31,f32])).

fof(f64,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f60,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (27301)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (27302)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (27314)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (27301)Refutation not found, incomplete strategy% (27301)------------------------------
% 0.22/0.48  % (27301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27301)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (27301)Memory used [KB]: 10490
% 0.22/0.48  % (27301)Time elapsed: 0.060 s
% 0.22/0.48  % (27301)------------------------------
% 0.22/0.48  % (27301)------------------------------
% 0.22/0.48  % (27308)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (27316)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (27307)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (27315)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (27306)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (27320)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (27318)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (27306)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f265,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f48,f52,f56,f60,f64,f84,f87,f94,f98,f110,f128,f135,f146,f163,f178,f230,f253])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    ~spl8_6 | spl8_1 | ~spl8_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f250,f228,f46,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl8_6 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl8_1 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl8_33 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl8_33),
% 0.22/0.50    inference(resolution,[],[f229,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  % (27303)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (27312)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (27305)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (27313)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (27317)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (27319)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (27310)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (27300)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (27311)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (27304)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(rectify,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1)) | ~spl8_33),
% 0.22/0.51    inference(avatar_component_clause,[],[f228])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    spl8_33 | ~spl8_18 | ~spl8_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f220,f176,f144,f228])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    spl8_18 <=> ! [X0] : (r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,X0)) | ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    spl8_24 <=> r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,sK1)) | (~spl8_18 | ~spl8_24)),
% 0.22/0.51    inference(resolution,[],[f145,f177])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | ~spl8_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f176])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,X0))) ) | ~spl8_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f144])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    ~spl8_5 | spl8_24 | ~spl8_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f172,f161,f176,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl8_5 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    spl8_21 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK1) | ~v1_relat_1(sK2) | ~spl8_21),
% 0.22/0.51    inference(resolution,[],[f162,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | r2_hidden(X5,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f44,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  % (27320)Refutation not found, incomplete strategy% (27320)------------------------------
% 0.22/0.51  % (27320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27320)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (27320)Memory used [KB]: 10490
% 0.22/0.51  % (27320)Time elapsed: 0.106 s
% 0.22/0.51  % (27320)------------------------------
% 0.22/0.51  % (27320)------------------------------
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(rectify,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK1)) | ~spl8_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f161])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    spl8_21 | ~spl8_2 | ~spl8_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f157,f92,f50,f161])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl8_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl8_8 <=> ! [X0] : (r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,X0)) | ~r1_tarski(sK0,X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK1)) | (~spl8_2 | ~spl8_8)),
% 0.22/0.51    inference(resolution,[],[f93,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    r1_tarski(sK0,sK1) | ~spl8_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f50])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_tarski(sK0,X0) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,X0))) ) | ~spl8_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ~spl8_4 | spl8_18 | ~spl8_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f140,f133,f144,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl8_4 <=> v1_relat_1(sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    spl8_16 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK3,X0)) | ~r2_hidden(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),X0) | ~v1_relat_1(sK3)) ) | ~spl8_16),
% 0.22/0.52    inference(resolution,[],[f134,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(X5,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f42,f40])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) | ~spl8_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f133])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl8_16 | ~spl8_3 | ~spl8_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f129,f126,f54,f133])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl8_3 <=> r1_tarski(sK2,sK3)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    spl8_15 <=> ! [X1] : (r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X1) | ~r1_tarski(sK2,X1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK3) | (~spl8_3 | ~spl8_15)),
% 0.22/0.52    inference(resolution,[],[f127,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    r1_tarski(sK2,sK3) | ~spl8_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f54])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X1] : (~r1_tarski(sK2,X1) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X1)) ) | ~spl8_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f126])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ~spl8_5 | spl8_15 | ~spl8_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f120,f108,f126,f62])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    spl8_11 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X1) | ~r1_tarski(sK2,X1) | ~v1_relat_1(sK2)) ) | ~spl8_11),
% 0.22/0.52    inference(resolution,[],[f109,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) | ~spl8_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f108])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    ~spl8_5 | spl8_11 | ~spl8_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f103,f96,f108,f62])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl8_9 <=> r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),sK2) | ~v1_relat_1(sK2) | ~spl8_9),
% 0.22/0.52    inference(resolution,[],[f97,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | r2_hidden(k4_tarski(X5,X6),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f43,f40])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) | ~spl8_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f96])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ~spl8_6 | spl8_9 | ~spl8_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f89,f82,f96,f79])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl8_7 <=> ! [X0] : (~r1_tarski(k7_relat_1(sK2,sK0),X0) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl8_7),
% 0.22/0.52    inference(resolution,[],[f83,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,X0) | ~v1_relat_1(X0) | r1_tarski(X0,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f33,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k7_relat_1(sK2,sK0),X0) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X0)) ) | ~spl8_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f82])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ~spl8_5 | spl8_8 | ~spl8_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f88,f82,f92,f62])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),k7_relat_1(sK2,X0)) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK2)) ) | ~spl8_7),
% 0.22/0.52    inference(resolution,[],[f83,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ~spl8_5 | spl8_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f85,f79,f62])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | spl8_6),
% 0.22/0.52    inference(resolution,[],[f80,f40])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl8_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~spl8_6 | spl8_7 | spl8_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f77,f46,f82,f79])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k7_relat_1(sK2,sK0),X0) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | r2_hidden(k4_tarski(sK4(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)),sK5(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),X0)) ) | spl8_1),
% 0.22/0.52    inference(resolution,[],[f74,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | spl8_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f46])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X2) | ~r1_tarski(X0,X2) | ~v1_relat_1(X0) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f31,f32])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    spl8_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f62])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f58])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl8_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f54])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    r1_tarski(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl8_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f50])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~spl8_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f46])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (27306)------------------------------
% 0.22/0.52  % (27306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27306)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (27306)Memory used [KB]: 10746
% 0.22/0.52  % (27306)Time elapsed: 0.086 s
% 0.22/0.52  % (27306)------------------------------
% 0.22/0.52  % (27306)------------------------------
% 0.22/0.52  % (27299)Success in time 0.151 s
%------------------------------------------------------------------------------
