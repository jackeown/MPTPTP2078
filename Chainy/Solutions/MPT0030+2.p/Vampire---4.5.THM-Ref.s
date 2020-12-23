%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0030+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 248 expanded)
%              Number of leaves         :   19 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  392 (1321 expanded)
%              Number of equality atoms :   34 ( 157 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2522,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f353,f428,f740,f837,f857,f858,f2285,f2336,f2346,f2367,f2369,f2396,f2479,f2519])).

fof(f2519,plain,
    ( spl19_42
    | ~ spl19_45 ),
    inference(avatar_contradiction_clause,[],[f2518])).

fof(f2518,plain,
    ( $false
    | spl19_42
    | ~ spl19_45 ),
    inference(subsumption_resolution,[],[f2497,f718])).

fof(f718,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | spl19_42 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl19_42
  <=> r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_42])])).

fof(f2497,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl19_45 ),
    inference(resolution,[],[f805,f275])).

fof(f275,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f246])).

fof(f246,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f154])).

fof(f154,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            | ~ r2_hidden(sK14(X0,X1,X2),X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK14(X0,X1,X2),X1)
              & r2_hidden(sK14(X0,X1,X2),X0) )
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f152,f153])).

fof(f153,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
          | ~ r2_hidden(sK14(X0,X1,X2),X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK14(X0,X1,X2),X1)
            & r2_hidden(sK14(X0,X1,X2),X0) )
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f152,plain,(
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
    inference(rectify,[],[f151])).

fof(f151,plain,(
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
    inference(flattening,[],[f150])).

fof(f150,plain,(
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

fof(f805,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl19_45 ),
    inference(avatar_component_clause,[],[f803])).

fof(f803,plain,
    ( spl19_45
  <=> r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_45])])).

fof(f2479,plain,
    ( spl19_41
    | ~ spl19_44 ),
    inference(avatar_contradiction_clause,[],[f2478])).

fof(f2478,plain,
    ( $false
    | spl19_41
    | ~ spl19_44 ),
    inference(subsumption_resolution,[],[f2457,f714])).

fof(f714,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | spl19_41 ),
    inference(avatar_component_clause,[],[f713])).

fof(f713,plain,
    ( spl19_41
  <=> r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_41])])).

fof(f2457,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl19_44 ),
    inference(resolution,[],[f801,f275])).

fof(f801,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl19_44 ),
    inference(avatar_component_clause,[],[f799])).

fof(f799,plain,
    ( spl19_44
  <=> r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_44])])).

fof(f2396,plain,
    ( spl19_44
    | spl19_45
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f2374,f346,f803,f799])).

fof(f346,plain,
    ( spl19_1
  <=> r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f2374,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl19_1 ),
    inference(resolution,[],[f348,f279])).

fof(f279,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f251])).

fof(f251,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f159])).

fof(f159,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
              & ~ r2_hidden(sK15(X0,X1,X2),X0) )
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( r2_hidden(sK15(X0,X1,X2),X1)
            | r2_hidden(sK15(X0,X1,X2),X0)
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f157,f158])).

fof(f158,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
            & ~ r2_hidden(sK15(X0,X1,X2),X0) )
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( r2_hidden(sK15(X0,X1,X2),X1)
          | r2_hidden(sK15(X0,X1,X2),X0)
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f157,plain,(
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
    inference(rectify,[],[f156])).

fof(f156,plain,(
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
    inference(flattening,[],[f155])).

fof(f155,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f348,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f346])).

fof(f2369,plain,
    ( spl19_1
    | spl19_3 ),
    inference(avatar_split_clause,[],[f2368,f355,f346])).

fof(f355,plain,
    ( spl19_3
  <=> r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f2368,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | spl19_3 ),
    inference(subsumption_resolution,[],[f2353,f283])).

fof(f283,plain,(
    ~ sQ18_eqProxy(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f165,f280])).

fof(f280,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f165,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f74,f112])).

fof(f112,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f55])).

fof(f55,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f2353,plain,
    ( sQ18_eqProxy(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | spl19_3 ),
    inference(resolution,[],[f356,f324])).

fof(f324,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f249,f280])).

fof(f249,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f154])).

fof(f356,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | spl19_3 ),
    inference(avatar_component_clause,[],[f355])).

fof(f2367,plain,
    ( ~ spl19_42
    | spl19_3 ),
    inference(avatar_split_clause,[],[f2352,f355,f717])).

fof(f2352,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | spl19_3 ),
    inference(resolution,[],[f356,f277])).

fof(f277,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f253])).

fof(f253,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f159])).

fof(f2346,plain,
    ( ~ spl19_1
    | ~ spl19_3
    | ~ spl19_4 ),
    inference(avatar_split_clause,[],[f2345,f361,f355,f346])).

fof(f361,plain,
    ( spl19_4
  <=> r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f2345,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl19_3
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f833,f430])).

fof(f430,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
        | r2_hidden(X0,sK0) )
    | ~ spl19_4 ),
    inference(resolution,[],[f362,f212])).

fof(f212,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f133,f134])).

fof(f134,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f362,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),sK0)
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f361])).

fof(f833,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f810,f283])).

fof(f810,plain,
    ( sQ18_eqProxy(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl19_3 ),
    inference(resolution,[],[f357,f323])).

fof(f323,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f250,f280])).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK14(X0,X1,X2),X1)
      | ~ r2_hidden(sK14(X0,X1,X2),X0)
      | ~ r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f154])).

fof(f357,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f355])).

fof(f2336,plain,
    ( ~ spl19_2
    | ~ spl19_42
    | spl19_45 ),
    inference(avatar_contradiction_clause,[],[f2335])).

fof(f2335,plain,
    ( $false
    | ~ spl19_2
    | ~ spl19_42
    | spl19_45 ),
    inference(subsumption_resolution,[],[f2334,f352])).

fof(f352,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl19_2
  <=> r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f2334,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_42
    | spl19_45 ),
    inference(subsumption_resolution,[],[f2320,f719])).

fof(f719,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl19_42 ),
    inference(avatar_component_clause,[],[f717])).

fof(f2320,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl19_45 ),
    inference(resolution,[],[f804,f274])).

fof(f274,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f247])).

fof(f247,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f154])).

fof(f804,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | spl19_45 ),
    inference(avatar_component_clause,[],[f803])).

fof(f2285,plain,
    ( ~ spl19_41
    | ~ spl19_2
    | spl19_44 ),
    inference(avatar_split_clause,[],[f2284,f799,f350,f713])).

fof(f2284,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl19_2
    | spl19_44 ),
    inference(subsumption_resolution,[],[f2267,f352])).

fof(f2267,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl19_44 ),
    inference(resolution,[],[f800,f274])).

fof(f800,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | spl19_44 ),
    inference(avatar_component_clause,[],[f799])).

fof(f858,plain,
    ( ~ spl19_45
    | spl19_1 ),
    inference(avatar_split_clause,[],[f841,f346,f803])).

fof(f841,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | spl19_1 ),
    inference(resolution,[],[f347,f277])).

fof(f347,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | spl19_1 ),
    inference(avatar_component_clause,[],[f346])).

fof(f857,plain,
    ( ~ spl19_44
    | spl19_1 ),
    inference(avatar_split_clause,[],[f840,f346,f799])).

fof(f840,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | spl19_1 ),
    inference(resolution,[],[f347,f278])).

fof(f278,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f252])).

fof(f252,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f159])).

fof(f837,plain,
    ( spl19_41
    | spl19_42
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f813,f355,f717,f713])).

fof(f813,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl19_3 ),
    inference(resolution,[],[f357,f279])).

fof(f740,plain,
    ( ~ spl19_41
    | spl19_3 ),
    inference(avatar_split_clause,[],[f724,f355,f713])).

fof(f724,plain,
    ( ~ r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | spl19_3 ),
    inference(resolution,[],[f356,f278])).

fof(f428,plain,(
    spl19_4 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl19_4 ),
    inference(subsumption_resolution,[],[f426,f182])).

fof(f182,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f426,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl19_4 ),
    inference(subsumption_resolution,[],[f419,f182])).

fof(f419,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl19_4 ),
    inference(resolution,[],[f363,f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f67])).

fof(f67,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f363,plain,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),sK0)
    | spl19_4 ),
    inference(avatar_component_clause,[],[f361])).

fof(f353,plain,
    ( spl19_1
    | spl19_2 ),
    inference(avatar_split_clause,[],[f332,f350,f346])).

fof(f332,plain,
    ( r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK14(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f283,f325])).

fof(f325,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f248,f280])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK14(X0,X1,X2),X0)
      | r2_hidden(sK14(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f154])).
%------------------------------------------------------------------------------
