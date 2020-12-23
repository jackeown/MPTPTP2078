%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    6
%              Number of atoms          :  173 ( 299 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f51,f55,f68,f78,f87,f94,f116,f171])).

fof(f171,plain,
    ( spl4_1
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl4_1
    | ~ spl4_18 ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k2_xboole_0(k4_xboole_0(sK2,sK0),sK1)
    | spl4_1
    | ~ spl4_18 ),
    inference(superposition,[],[f25,f115])).

fof(f115,plain,
    ( ! [X1] : k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_18
  <=> ! [X1] : k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f25,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl4_1
  <=> k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f116,plain,
    ( spl4_18
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f100,f91,f53,f114])).

fof(f53,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f91,plain,
    ( spl4_14
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f100,plain,
    ( ! [X1] : k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1)
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(superposition,[],[f54,f93])).

fof(f93,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f54,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f94,plain,
    ( spl4_14
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f89,f84,f49,f91])).

fof(f49,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f84,plain,
    ( spl4_13
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f89,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(resolution,[],[f86,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f86,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f87,plain,
    ( spl4_13
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f82,f76,f37,f84])).

fof(f37,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f76,plain,
    ( spl4_12
  <=> ! [X1] :
        ( ~ r2_hidden(sK3(sK1,X1),sK0)
        | r1_xboole_0(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f82,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,
    ( r1_xboole_0(sK1,sK0)
    | r1_xboole_0(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(resolution,[],[f77,f38])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f77,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK1,X1),sK0)
        | r1_xboole_0(sK1,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl4_12
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f70,f66,f41,f76])).

fof(f41,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f66,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f70,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK1,X1),sK0)
        | r1_xboole_0(sK1,X1) )
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f67,f42])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f64,f33,f28,f66])).

fof(f28,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f33,plain,
    ( spl4_3
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f34,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f55,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f51,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f43,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f39,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
        & r1_xboole_0(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f23])).

fof(f15,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (29018)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (29018)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f172,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f51,f55,f68,f78,f87,f94,f116,f171])).
% 0.21/0.42  fof(f171,plain,(
% 0.21/0.42    spl4_1 | ~spl4_18),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.42  fof(f170,plain,(
% 0.21/0.42    $false | (spl4_1 | ~spl4_18)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f165])).
% 0.21/0.42  fof(f165,plain,(
% 0.21/0.42    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) | (spl4_1 | ~spl4_18)),
% 0.21/0.42    inference(superposition,[],[f25,f115])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    ( ! [X1] : (k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1)) ) | ~spl4_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f114])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    spl4_18 <=> ! [X1] : k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    spl4_1 <=> k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl4_18 | ~spl4_8 | ~spl4_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f100,f91,f53,f114])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    spl4_8 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl4_14 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ( ! [X1] : (k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1)) ) | (~spl4_8 | ~spl4_14)),
% 0.21/0.42    inference(superposition,[],[f54,f93])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    sK1 = k4_xboole_0(sK1,sK0) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f91])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f53])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl4_14 | ~spl4_7 | ~spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f89,f84,f49,f91])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl4_13 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    sK1 = k4_xboole_0(sK1,sK0) | (~spl4_7 | ~spl4_13)),
% 0.21/0.42    inference(resolution,[],[f86,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f49])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK0) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f84])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl4_13 | ~spl4_4 | ~spl4_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f82,f76,f37,f84])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl4_4 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl4_12 <=> ! [X1] : (~r2_hidden(sK3(sK1,X1),sK0) | r1_xboole_0(sK1,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK0) | (~spl4_4 | ~spl4_12)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK0) | r1_xboole_0(sK1,sK0) | (~spl4_4 | ~spl4_12)),
% 0.21/0.42    inference(resolution,[],[f77,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(sK3(sK1,X1),sK0) | r1_xboole_0(sK1,X1)) ) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl4_12 | ~spl4_5 | ~spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f70,f66,f41,f76])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl4_5 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl4_10 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(sK3(sK1,X1),sK0) | r1_xboole_0(sK1,X1)) ) | (~spl4_5 | ~spl4_10)),
% 0.21/0.42    inference(resolution,[],[f67,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_10 | ~spl4_2 | ~spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f33,f28,f66])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl4_2 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl4_3 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.42    inference(resolution,[],[f34,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f33])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f53])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f49])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f41])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f33])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f28])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f23])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (29018)------------------------------
% 0.21/0.42  % (29018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (29018)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (29018)Memory used [KB]: 10618
% 0.21/0.42  % (29018)Time elapsed: 0.008 s
% 0.21/0.42  % (29018)------------------------------
% 0.21/0.42  % (29018)------------------------------
% 0.21/0.42  % (29012)Success in time 0.066 s
%------------------------------------------------------------------------------
