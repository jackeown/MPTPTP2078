%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0023+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 209 expanded)
%              Number of leaves         :   11 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 (1158 expanded)
%              Number of equality atoms :   23 ( 147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f326,f801,f819,f821,f848,f849,f1144,f1145,f1201,f1202,f1222,f1297])).

fof(f1297,plain,
    ( ~ spl18_3
    | spl18_21
    | ~ spl18_34 ),
    inference(avatar_contradiction_clause,[],[f1296])).

fof(f1296,plain,
    ( $false
    | ~ spl18_3
    | spl18_21
    | ~ spl18_34 ),
    inference(subsumption_resolution,[],[f1295,f768])).

fof(f768,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl18_34 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl18_34
  <=> r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_34])])).

fof(f1295,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl18_3
    | spl18_21 ),
    inference(subsumption_resolution,[],[f1281,f325])).

fof(f325,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl18_3 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl18_3
  <=> r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f1281,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | spl18_21 ),
    inference(resolution,[],[f525,f251])).

% (25142)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
fof(f251,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f224])).

fof(f224,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f140])).

% (25144)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
fof(f140,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f138,f139])).

fof(f139,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f138,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f137])).

fof(f137,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f136])).

fof(f136,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f525,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | spl18_21 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl18_21
  <=> r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_21])])).

fof(f1222,plain,
    ( ~ spl18_21
    | spl18_1
    | ~ spl18_20 ),
    inference(avatar_split_clause,[],[f1221,f519,f314,f523])).

fof(f314,plain,
    ( spl18_1
  <=> r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_1])])).

fof(f519,plain,
    ( spl18_20
  <=> r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).

fof(f1221,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | spl18_1
    | ~ spl18_20 ),
    inference(subsumption_resolution,[],[f1205,f520])).

fof(f520,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl18_20 ),
    inference(avatar_component_clause,[],[f519])).

fof(f1205,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | spl18_1 ),
    inference(resolution,[],[f315,f251])).

fof(f315,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl18_1 ),
    inference(avatar_component_clause,[],[f314])).

fof(f1202,plain,
    ( spl18_34
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f1178,f318,f767])).

fof(f318,plain,
    ( spl18_2
  <=> r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f1178,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl18_2 ),
    inference(resolution,[],[f320,f252])).

fof(f252,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f223])).

fof(f223,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f140])).

fof(f320,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f318])).

fof(f1201,plain,
    ( ~ spl18_1
    | ~ spl18_2
    | ~ spl18_3 ),
    inference(avatar_split_clause,[],[f1200,f323,f318,f314])).

fof(f1200,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl18_2
    | ~ spl18_3 ),
    inference(subsumption_resolution,[],[f1199,f325])).

fof(f1199,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl18_2 ),
    inference(subsumption_resolution,[],[f1176,f260])).

fof(f260,plain,(
    ~ sQ17_eqProxy(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f151,f257])).

fof(f257,plain,(
    ! [X1,X0] :
      ( sQ17_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ17_eqProxy])])).

fof(f151,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f67,f100])).

fof(f100,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) != k3_xboole_0(X0,k3_xboole_0(X1,X2))
   => k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) != k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f46])).

fof(f46,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f1176,plain,
    ( sQ17_eqProxy(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl18_2 ),
    inference(resolution,[],[f320,f294])).

fof(f294,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f227,f257])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK13(X0,X1,X2),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X0)
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f1145,plain,
    ( spl18_34
    | ~ spl18_21 ),
    inference(avatar_split_clause,[],[f1116,f523,f767])).

fof(f1116,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl18_21 ),
    inference(resolution,[],[f524,f253])).

fof(f253,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f222])).

fof(f222,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f140])).

fof(f524,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl18_21 ),
    inference(avatar_component_clause,[],[f523])).

fof(f1144,plain,
    ( spl18_3
    | ~ spl18_21 ),
    inference(avatar_split_clause,[],[f1117,f523,f323])).

fof(f1117,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl18_21 ),
    inference(resolution,[],[f524,f252])).

fof(f849,plain,
    ( spl18_21
    | ~ spl18_1 ),
    inference(avatar_split_clause,[],[f827,f314,f523])).

% (25132)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
fof(f827,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl18_1 ),
    inference(resolution,[],[f316,f252])).

fof(f316,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl18_1 ),
    inference(avatar_component_clause,[],[f314])).

fof(f848,plain,
    ( spl18_20
    | ~ spl18_1 ),
    inference(avatar_split_clause,[],[f826,f314,f519])).

fof(f826,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl18_1 ),
    inference(resolution,[],[f316,f253])).

fof(f821,plain,
    ( spl18_1
    | spl18_2 ),
    inference(avatar_split_clause,[],[f820,f318,f314])).

fof(f820,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl18_2 ),
    inference(subsumption_resolution,[],[f805,f260])).

fof(f805,plain,
    ( sQ17_eqProxy(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl18_2 ),
    inference(resolution,[],[f319,f296])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f225,f257])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X0)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f319,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | spl18_2 ),
    inference(avatar_component_clause,[],[f318])).

fof(f819,plain,
    ( ~ spl18_20
    | ~ spl18_34
    | spl18_2 ),
    inference(avatar_split_clause,[],[f804,f318,f767,f519])).

fof(f804,plain,
    ( ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | spl18_2 ),
    inference(resolution,[],[f319,f251])).

fof(f801,plain,
    ( spl18_20
    | ~ spl18_2 ),
    inference(avatar_split_clause,[],[f472,f318,f519])).

fof(f472,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl18_2 ),
    inference(resolution,[],[f320,f253])).

fof(f326,plain,
    ( spl18_1
    | spl18_3 ),
    inference(avatar_split_clause,[],[f304,f323,f314])).

fof(f304,plain,
    ( r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK13(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f260,f295])).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( sQ17_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f226,f257])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f140])).
%------------------------------------------------------------------------------
