%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 225 expanded)
%              Number of leaves         :   14 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  315 (1310 expanded)
%              Number of equality atoms :   35 ( 167 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f63,f85,f110,f115,f125,f131,f145,f146,f147,f162,f182,f183])).

fof(f183,plain,
    ( ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f157,f112,f78])).

fof(f78,plain,
    ( spl6_4
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f112,plain,
    ( spl6_6
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f157,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f113,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f113,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f182,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f176,f59,f78])).

fof(f59,plain,
    ( spl6_3
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f176,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f36])).

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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f60,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f162,plain,
    ( spl6_7
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f156,f112,f122])).

fof(f122,plain,
    ( spl6_7
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f156,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f113,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f147,plain,
    ( ~ spl6_7
    | ~ spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f133,f54,f82,f122])).

fof(f82,plain,
    ( spl6_5
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f133,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0)
    | spl6_2 ),
    inference(resolution,[],[f55,f34])).

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

fof(f55,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f146,plain,
    ( spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f140,f50,f82])).

fof(f50,plain,
    ( spl6_1
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f140,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f35])).

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

fof(f52,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f145,plain,
    ( spl6_6
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f139,f50,f112])).

fof(f139,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f36])).

fof(f131,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl6_2
    | spl6_7 ),
    inference(resolution,[],[f124,f65])).

fof(f65,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f124,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( ~ spl6_7
    | spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f116,f112,f78,f122])).

fof(f116,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0)
    | spl6_6 ),
    inference(resolution,[],[f114,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f114,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f88,f50,f82,f112])).

fof(f88,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2))
    | spl6_1 ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f110,plain,
    ( ~ spl6_2
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl6_2
    | spl6_5 ),
    inference(resolution,[],[f84,f66])).

fof(f66,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f35])).

fof(f84,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_3 ),
    inference(avatar_split_clause,[],[f72,f59,f82,f78])).

fof(f72,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2)
    | spl6_3 ),
    inference(resolution,[],[f61,f34])).

fof(f61,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f48,f59,f54,f50])).

fof(f48,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f24,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ~ sQ5_eqProxy(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)
   => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f62,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f47,f59,f50])).

fof(f47,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f23,f37])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f54,f50])).

fof(f46,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f22,f37])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (4454)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (4446)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (4454)Refutation not found, incomplete strategy% (4454)------------------------------
% 0.21/0.48  % (4454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4454)Memory used [KB]: 6012
% 0.21/0.48  % (4454)Time elapsed: 0.066 s
% 0.21/0.48  % (4454)------------------------------
% 0.21/0.48  % (4454)------------------------------
% 0.21/0.48  % (4440)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (4440)Refutation not found, incomplete strategy% (4440)------------------------------
% 0.21/0.48  % (4440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4440)Memory used [KB]: 10490
% 0.21/0.48  % (4440)Time elapsed: 0.060 s
% 0.21/0.48  % (4440)------------------------------
% 0.21/0.48  % (4440)------------------------------
% 0.21/0.48  % (4441)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (4453)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (4451)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (4453)Refutation not found, incomplete strategy% (4453)------------------------------
% 0.21/0.49  % (4453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4453)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (4453)Memory used [KB]: 10618
% 0.21/0.49  % (4453)Time elapsed: 0.030 s
% 0.21/0.49  % (4453)------------------------------
% 0.21/0.49  % (4453)------------------------------
% 0.21/0.49  % (4448)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (4451)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f57,f62,f63,f85,f110,f115,f125,f131,f145,f146,f147,f162,f182,f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ~spl6_4 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f157,f112,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl6_4 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl6_6 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f113,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(rectify,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2)) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl6_4 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f176,f59,f78])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl6_3 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f60,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(rectify,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1)) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl6_7 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f156,f112,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl6_7 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f113,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~spl6_7 | ~spl6_5 | spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f133,f54,f82,f122])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl6_5 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl6_2 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0) | spl6_2),
% 0.21/0.49    inference(resolution,[],[f55,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1)) | spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl6_5 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f50,f82])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl6_1 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f52,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl6_6 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f139,f50,f112])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2)) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f52,f36])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~spl6_2 | spl6_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    $false | (~spl6_2 | spl6_7)),
% 0.21/0.49    inference(resolution,[],[f124,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f56,f36])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1)) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0) | spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~spl6_7 | spl6_4 | spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f116,f112,f78,f122])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK0) | spl6_6),
% 0.21/0.49    inference(resolution,[],[f114,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2)) | spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~spl6_6 | ~spl6_5 | spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f88,f50,f82,f112])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k4_xboole_0(sK0,sK2)) | spl6_1),
% 0.21/0.49    inference(resolution,[],[f51,f34])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)) | spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~spl6_2 | spl6_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    $false | (~spl6_2 | spl6_5)),
% 0.21/0.49    inference(resolution,[],[f84,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f56,f35])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1) | spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~spl6_4 | ~spl6_5 | spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f72,f59,f82,f78])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK1) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),sK2) | spl6_3),
% 0.21/0.49    inference(resolution,[],[f61,f34])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1)) | spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_2 | spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f59,f54,f50])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1)) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 0.21/0.49    inference(resolution,[],[f38,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sQ5_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f24,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~sQ5_eqProxy(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f18,f37])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl6_1 | ~spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f59,f50])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1)) | r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 0.21/0.49    inference(resolution,[],[f38,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sQ5_eqProxy(k4_xboole_0(X0,X1),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f23,f37])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl6_1 | spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f54,f50])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 0.21/0.49    inference(resolution,[],[f38,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sQ5_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f22,f37])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (4451)------------------------------
% 0.21/0.49  % (4451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4451)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (4451)Memory used [KB]: 6140
% 0.21/0.49  % (4451)Time elapsed: 0.077 s
% 0.21/0.49  % (4451)------------------------------
% 0.21/0.49  % (4451)------------------------------
% 0.21/0.49  % (4438)Success in time 0.134 s
%------------------------------------------------------------------------------
