%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0030+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 227 expanded)
%              Number of leaves         :   14 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 (1373 expanded)
%              Number of equality atoms :   35 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f63,f83,f117,f131,f144,f163,f178,f179,f180,f183,f184])).

% (19801)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f184,plain,
    ( spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f171,f160,f54])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f160,plain,
    ( spl6_8
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f171,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f162,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f162,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f183,plain,
    ( spl6_5
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f172,f160,f80])).

fof(f80,plain,
    ( spl6_5
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f172,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f162,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,
    ( spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f164,f156,f54])).

fof(f156,plain,
    ( spl6_7
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f164,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f158,f36])).

fof(f158,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f156])).

fof(f179,plain,
    ( spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f165,f156,f76])).

fof(f76,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f165,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f158,f35])).

fof(f178,plain,
    ( ~ spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f138,f59,f76])).

fof(f59,plain,
    ( spl6_3
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f138,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | spl6_3 ),
    inference(resolution,[],[f60,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f60,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

% (19801)Refutation not found, incomplete strategy% (19801)------------------------------
% (19801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19801)Termination reason: Refutation not found, incomplete strategy

% (19801)Memory used [KB]: 10490
% (19801)Time elapsed: 0.102 s
% (19801)------------------------------
% (19801)------------------------------
fof(f163,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f150,f50,f160,f156])).

fof(f50,plain,
    ( spl6_1
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f150,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f144,plain,
    ( ~ spl6_5
    | spl6_3 ),
    inference(avatar_split_clause,[],[f139,f59,f80])).

fof(f139,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | spl6_3 ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f131,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f126,f50,f80,f54])).

fof(f126,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl6_1 ),
    inference(resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | spl6_1 ),
    inference(resolution,[],[f51,f31])).

fof(f51,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f117,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f112,f50,f76,f54])).

fof(f112,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl6_1 ),
    inference(resolution,[],[f86,f34])).

fof(f86,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f51,f32])).

fof(f83,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f70,f59,f80,f76])).

fof(f70,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f61,f33])).

fof(f61,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f48,f59,f54,f50])).

fof(f48,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f30,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ~ sQ5_eqProxy(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f62,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f47,f59,f50])).

fof(f47,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f54,f50])).

fof(f46,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
