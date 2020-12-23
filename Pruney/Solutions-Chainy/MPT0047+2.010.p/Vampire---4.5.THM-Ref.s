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
% DateTime   : Thu Dec  3 12:29:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 138 expanded)
%              Number of leaves         :   11 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 761 expanded)
%              Number of equality atoms :   34 ( 107 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f63,f85,f115,f133,f134,f157])).

fof(f157,plain,
    ( spl5_2
    | spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f152,f82,f59,f54])).

fof(f54,plain,
    ( spl5_2
  <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f59,plain,
    ( spl5_3
  <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f152,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1)
    | r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f83,f33])).

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

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
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

fof(f83,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f134,plain,
    ( spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f127,f50,f82])).

fof(f50,plain,
    ( spl5_1
  <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f127,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f52,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f133,plain,
    ( ~ spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f128,f50,f59])).

fof(f128,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f115,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl5_2
    | spl5_4 ),
    inference(resolution,[],[f84,f67])).

fof(f67,plain,
    ( ! [X2] : r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,X2))
    | ~ spl5_2 ),
    inference(resolution,[],[f56,f32])).

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

fof(f56,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f84,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( ~ spl5_4
    | spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f76,f50,f59,f82])).

fof(f76,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f63,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f48,f59,f54,f50])).

fof(f48,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f30,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ~ sQ4_eqProxy(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1)
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f62,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f47,f59,f50])).

fof(f47,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1)
    | r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f46,f54,f50])).

fof(f46,plain,
    ( r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0)
    | r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:31:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (8948)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.42  % (8948)Refutation not found, incomplete strategy% (8948)------------------------------
% 0.22/0.42  % (8948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (8948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.42  
% 0.22/0.42  % (8948)Memory used [KB]: 1535
% 0.22/0.42  % (8948)Time elapsed: 0.003 s
% 0.22/0.42  % (8948)------------------------------
% 0.22/0.42  % (8948)------------------------------
% 0.22/0.46  % (8950)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (8950)Refutation not found, incomplete strategy% (8950)------------------------------
% 0.22/0.47  % (8950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (8950)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (8950)Memory used [KB]: 6012
% 0.22/0.47  % (8950)Time elapsed: 0.042 s
% 0.22/0.47  % (8950)------------------------------
% 0.22/0.47  % (8950)------------------------------
% 0.22/0.49  % (8955)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (8955)Refutation not found, incomplete strategy% (8955)------------------------------
% 0.22/0.50  % (8955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8955)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8955)Memory used [KB]: 10490
% 0.22/0.50  % (8955)Time elapsed: 0.063 s
% 0.22/0.50  % (8955)------------------------------
% 0.22/0.50  % (8955)------------------------------
% 0.22/0.50  % (8935)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (8935)Refutation not found, incomplete strategy% (8935)------------------------------
% 0.22/0.50  % (8935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8935)Memory used [KB]: 6140
% 0.22/0.50  % (8935)Time elapsed: 0.071 s
% 0.22/0.50  % (8935)------------------------------
% 0.22/0.50  % (8935)------------------------------
% 0.22/0.50  % (8949)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (8949)Refutation not found, incomplete strategy% (8949)------------------------------
% 0.22/0.51  % (8949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8949)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8949)Memory used [KB]: 10618
% 0.22/0.51  % (8949)Time elapsed: 0.036 s
% 0.22/0.51  % (8949)------------------------------
% 0.22/0.51  % (8949)------------------------------
% 0.22/0.51  % (8942)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (8941)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (8947)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (8951)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (8940)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (8936)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (8936)Refutation not found, incomplete strategy% (8936)------------------------------
% 0.22/0.53  % (8936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8936)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8936)Memory used [KB]: 10490
% 0.22/0.53  % (8936)Time elapsed: 0.097 s
% 0.22/0.53  % (8936)------------------------------
% 0.22/0.53  % (8936)------------------------------
% 0.22/0.54  % (8943)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.54  % (8947)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f57,f62,f63,f85,f115,f133,f134,f157])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    spl5_2 | spl5_3 | ~spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f152,f82,f59,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    spl5_2 <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    spl5_3 <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    spl5_4 <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1) | r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0) | ~spl5_4),
% 0.22/0.54    inference(resolution,[],[f83,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1)) | ~spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f82])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl5_4 | ~spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f127,f50,f82])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    spl5_1 <=> r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1)) | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f52,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f50])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ~spl5_3 | ~spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f128,f50,f59])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1) | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f52,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    ~spl5_2 | spl5_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    $false | (~spl5_2 | spl5_4)),
% 0.22/0.54    inference(resolution,[],[f84,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2] : (r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,X2))) ) | ~spl5_2),
% 0.22/0.54    inference(resolution,[],[f56,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0) | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f54])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1)) | spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f82])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ~spl5_4 | spl5_3 | spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f76,f50,f59,f82])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1) | ~r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k2_xboole_0(sK0,sK1)) | spl5_1),
% 0.22/0.54    inference(resolution,[],[f51,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f50])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_2 | spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f48,f59,f54,f50])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1) | ~r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0) | ~r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1))),
% 0.22/0.54    inference(resolution,[],[f38,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sQ4_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f30,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ~sQ4_eqProxy(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1))),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f18,f37])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.22/0.54  fof(f6,plain,(
% 0.22/0.54    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1) => k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f5,plain,(
% 0.22/0.54    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.54    inference(negated_conjecture,[],[f3])).
% 0.22/0.54  fof(f3,conjecture,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    spl5_1 | ~spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f59,f50])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK1) | r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1))),
% 0.22/0.54    inference(resolution,[],[f38,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sQ4_eqProxy(k4_xboole_0(X0,X1),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f29,f37])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    spl5_1 | spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f54,f50])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),sK0) | r2_hidden(sK3(sK0,sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK1))),
% 0.22/0.54    inference(resolution,[],[f38,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sQ4_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f28,f37])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (8947)------------------------------
% 0.22/0.54  % (8947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8947)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (8947)Memory used [KB]: 6140
% 0.22/0.54  % (8947)Time elapsed: 0.096 s
% 0.22/0.54  % (8947)------------------------------
% 0.22/0.54  % (8947)------------------------------
% 0.22/0.54  % (8934)Success in time 0.179 s
%------------------------------------------------------------------------------
