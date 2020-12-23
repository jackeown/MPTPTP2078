%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0031+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 263 expanded)
%              Number of leaves         :   19 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  412 (1357 expanded)
%              Number of equality atoms :   34 ( 157 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f431,f1212,f2035,f2062,f2089,f2125,f2128,f2171,f2172,f2236,f2277,f2299,f2302,f2327,f2369])).

fof(f2369,plain,
    ( spl19_2
    | ~ spl19_42
    | spl19_67 ),
    inference(avatar_contradiction_clause,[],[f2368])).

fof(f2368,plain,
    ( $false
    | spl19_2
    | ~ spl19_42
    | spl19_67 ),
    inference(subsumption_resolution,[],[f2367,f354])).

fof(f354,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | spl19_2 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl19_2
  <=> r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f2367,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_42
    | spl19_67 ),
    inference(subsumption_resolution,[],[f2345,f1177])).

fof(f1177,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | spl19_67 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1175,plain,
    ( spl19_67
  <=> r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_67])])).

fof(f2345,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_42 ),
    inference(resolution,[],[f756,f281])).

fof(f281,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f253])).

fof(f253,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f160])).

fof(f160,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f158,f159])).

fof(f159,plain,(
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

fof(f158,plain,(
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
    inference(rectify,[],[f157])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f156])).

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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f756,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl19_42 ),
    inference(avatar_component_clause,[],[f755])).

fof(f755,plain,
    ( spl19_42
  <=> r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_42])])).

fof(f2327,plain,
    ( spl19_42
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f2306,f349,f755])).

fof(f349,plain,
    ( spl19_1
  <=> r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f2306,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl19_1 ),
    inference(resolution,[],[f351,f277])).

fof(f277,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f248])).

fof(f248,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f155])).

fof(f155,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f153,f154])).

fof(f154,plain,(
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

fof(f153,plain,(
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
    inference(rectify,[],[f152])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f151])).

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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f351,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f349])).

fof(f2302,plain,
    ( spl19_1
    | spl19_2
    | spl19_3 ),
    inference(avatar_split_clause,[],[f2301,f357,f353,f349])).

fof(f357,plain,
    ( spl19_3
  <=> r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f2301,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | spl19_2
    | spl19_3 ),
    inference(subsumption_resolution,[],[f2300,f354])).

fof(f2300,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | spl19_3 ),
    inference(subsumption_resolution,[],[f2284,f285])).

fof(f285,plain,(
    ~ sQ18_eqProxy(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f166,f282])).

fof(f282,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f166,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f75,f113])).

fof(f113,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))
   => k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f56])).

fof(f56,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f2284,plain,
    ( sQ18_eqProxy(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | spl19_3 ),
    inference(resolution,[],[f358,f331])).

fof(f331,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK15(X0,X1,X2),X1)
      | r2_hidden(sK15(X0,X1,X2),X0)
      | r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f256,f282])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK15(X0,X1,X2),X1)
      | r2_hidden(sK15(X0,X1,X2),X0)
      | r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f358,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | spl19_3 ),
    inference(avatar_component_clause,[],[f357])).

fof(f2299,plain,
    ( ~ spl19_67
    | spl19_3
    | ~ spl19_66 ),
    inference(avatar_split_clause,[],[f2298,f1171,f357,f1175])).

fof(f1171,plain,
    ( spl19_66
  <=> r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_66])])).

fof(f2298,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | spl19_3
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f2283,f1172])).

fof(f1172,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl19_66 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f2283,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | spl19_3 ),
    inference(resolution,[],[f358,f276])).

fof(f276,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f249])).

fof(f249,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f155])).

fof(f2277,plain,
    ( spl19_42
    | ~ spl19_67 ),
    inference(avatar_contradiction_clause,[],[f2276])).

fof(f2276,plain,
    ( $false
    | spl19_42
    | ~ spl19_67 ),
    inference(subsumption_resolution,[],[f2262,f1176])).

fof(f1176,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | ~ spl19_67 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f2262,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | spl19_42 ),
    inference(resolution,[],[f757,f279])).

fof(f279,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f255])).

fof(f255,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f160])).

fof(f757,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | spl19_42 ),
    inference(avatar_component_clause,[],[f755])).

fof(f2236,plain,
    ( spl19_41
    | ~ spl19_66 ),
    inference(avatar_contradiction_clause,[],[f2235])).

fof(f2235,plain,
    ( $false
    | spl19_41
    | ~ spl19_66 ),
    inference(subsumption_resolution,[],[f2221,f1172])).

fof(f2221,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | spl19_41 ),
    inference(resolution,[],[f753,f279])).

fof(f753,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | spl19_41 ),
    inference(avatar_component_clause,[],[f751])).

fof(f751,plain,
    ( spl19_41
  <=> r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_41])])).

fof(f2172,plain,
    ( spl19_67
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f2150,f357,f1175])).

fof(f2150,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | ~ spl19_3 ),
    inference(resolution,[],[f359,f277])).

fof(f359,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f357])).

fof(f2171,plain,
    ( spl19_66
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f2149,f357,f1171])).

fof(f2149,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl19_3 ),
    inference(resolution,[],[f359,f278])).

fof(f278,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f247])).

fof(f247,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f155])).

fof(f2128,plain,
    ( ~ spl19_2
    | spl19_1
    | ~ spl19_4 ),
    inference(avatar_split_clause,[],[f2107,f364,f349,f353])).

fof(f364,plain,
    ( spl19_4
  <=> r1_tarski(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f2107,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | spl19_1
    | ~ spl19_4 ),
    inference(resolution,[],[f350,f433])).

fof(f433,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl19_4 ),
    inference(resolution,[],[f365,f213])).

fof(f213,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f134,f135])).

fof(f135,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f90])).

fof(f90,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f365,plain,
    ( r1_tarski(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f364])).

fof(f350,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | spl19_1 ),
    inference(avatar_component_clause,[],[f349])).

fof(f2125,plain,
    ( ~ spl19_41
    | ~ spl19_42
    | spl19_1 ),
    inference(avatar_split_clause,[],[f2108,f349,f755,f751])).

fof(f2108,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | spl19_1 ),
    inference(resolution,[],[f350,f276])).

fof(f2089,plain,
    ( ~ spl19_1
    | ~ spl19_2 ),
    inference(avatar_split_clause,[],[f2088,f353,f349])).

fof(f2088,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ spl19_2 ),
    inference(subsumption_resolution,[],[f2068,f285])).

fof(f2068,plain,
    ( sQ18_eqProxy(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ spl19_2 ),
    inference(resolution,[],[f355,f330])).

fof(f330,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK15(X0,X1,X2),X0)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f257,f282])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK15(X0,X1,X2),X0)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f355,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f353])).

fof(f2062,plain,
    ( ~ spl19_1
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f2061,f357,f349])).

fof(f2061,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f2038,f285])).

fof(f2038,plain,
    ( sQ18_eqProxy(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ spl19_3 ),
    inference(resolution,[],[f359,f329])).

fof(f329,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK15(X0,X1,X2),X1)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f258,f282])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK15(X0,X1,X2),X1)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f2035,plain,
    ( spl19_2
    | ~ spl19_41
    | spl19_66 ),
    inference(avatar_contradiction_clause,[],[f2034])).

fof(f2034,plain,
    ( $false
    | spl19_2
    | ~ spl19_41
    | spl19_66 ),
    inference(subsumption_resolution,[],[f2033,f354])).

fof(f2033,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_41
    | spl19_66 ),
    inference(subsumption_resolution,[],[f2011,f1173])).

fof(f1173,plain,
    ( ~ r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | spl19_66 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f2011,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl19_41 ),
    inference(resolution,[],[f752,f281])).

fof(f752,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl19_41 ),
    inference(avatar_component_clause,[],[f751])).

fof(f1212,plain,
    ( spl19_41
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f1190,f349,f751])).

fof(f1190,plain,
    ( r2_hidden(sK15(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl19_1 ),
    inference(resolution,[],[f351,f278])).

fof(f431,plain,(
    spl19_4 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | spl19_4 ),
    inference(subsumption_resolution,[],[f429,f182])).

fof(f182,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f429,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl19_4 ),
    inference(subsumption_resolution,[],[f422,f182])).

fof(f422,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl19_4 ),
    inference(resolution,[],[f366,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f366,plain,
    ( ~ r1_tarski(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | spl19_4 ),
    inference(avatar_component_clause,[],[f364])).
%------------------------------------------------------------------------------
