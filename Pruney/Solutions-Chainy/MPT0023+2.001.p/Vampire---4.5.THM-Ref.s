%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 196 expanded)
%              Number of leaves         :   11 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  210 (1126 expanded)
%              Number of equality atoms :   23 ( 147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f45,f67,f75,f83,f91,f100,f105,f106,f107,f121])).

fof(f121,plain,
    ( ~ spl5_4
    | ~ spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f118,f36,f80,f60])).

fof(f60,plain,
    ( spl5_4
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f80,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f36,plain,
    ( spl5_2
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f118,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | spl5_2 ),
    inference(resolution,[],[f37,f19])).

fof(f19,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f10])).

fof(f10,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f37,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f107,plain,
    ( spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f96,f32,f60])).

fof(f32,plain,
    ( spl5_1
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f96,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f106,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f101,f64,f80])).

fof(f64,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f101,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f65,f21])).

fof(f65,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f105,plain,
    ( spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f102,f64,f41])).

fof(f41,plain,
    ( spl5_3
  <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f65,f20])).

fof(f20,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f100,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f97,f32,f64])).

fof(f97,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f34,f20])).

fof(f91,plain,
    ( ~ spl5_2
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl5_2
    | spl5_6 ),
    inference(resolution,[],[f82,f51])).

fof(f51,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f20])).

fof(f38,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f82,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,
    ( ~ spl5_6
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f76,f64,f41,f80])).

fof(f76,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)
    | spl5_5 ),
    inference(resolution,[],[f66,f19])).

fof(f66,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f75,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl5_2
    | spl5_4 ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f21])).

fof(f62,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f67,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f56,f32,f64,f60])).

fof(f56,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)
    | spl5_1 ),
    inference(resolution,[],[f33,f19])).

fof(f33,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f45,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f30,f41,f36,f32])).

fof(f30,plain,
    ( ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f18,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ~ sQ4_eqProxy(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f12,f22])).

fof(f12,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) != k3_xboole_0(X0,k3_xboole_0(X1,X2))
   => k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) != k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f44,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f29,f41,f32])).

fof(f29,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f23,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f17,f22])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f28,f36,f32])).

fof(f28,plain,
    ( r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f16,f22])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (31586)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.42  % (31586)Refutation not found, incomplete strategy% (31586)------------------------------
% 0.21/0.42  % (31586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (31586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (31586)Memory used [KB]: 10490
% 0.21/0.43  % (31586)Time elapsed: 0.036 s
% 0.21/0.43  % (31586)------------------------------
% 0.21/0.43  % (31586)------------------------------
% 0.21/0.43  % (31595)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.44  % (31595)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f39,f44,f45,f67,f75,f83,f91,f100,f105,f106,f107,f121])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    ~spl5_4 | ~spl5_6 | spl5_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f118,f36,f80,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    spl5_4 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    spl5_6 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl5_2 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0) | spl5_2),
% 0.21/0.44    inference(resolution,[],[f37,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.44    inference(rectify,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.44    inference(nnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) | spl5_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f36])).
% 0.21/0.44  fof(f107,plain,(
% 0.21/0.44    spl5_4 | ~spl5_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f96,f32,f60])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    spl5_1 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0) | ~spl5_1),
% 0.21/0.44    inference(resolution,[],[f34,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(equality_resolution,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | ~spl5_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl5_6 | ~spl5_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f101,f64,f80])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl5_5 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1) | ~spl5_5),
% 0.21/0.44    inference(resolution,[],[f65,f21])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) | ~spl5_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    spl5_3 | ~spl5_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f102,f64,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl5_3 <=> r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) | ~spl5_5),
% 0.21/0.44    inference(resolution,[],[f65,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(equality_resolution,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl5_5 | ~spl5_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f97,f32,f64])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) | ~spl5_1),
% 0.21/0.44    inference(resolution,[],[f34,f20])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    ~spl5_2 | spl5_6),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    $false | (~spl5_2 | spl5_6)),
% 0.21/0.44    inference(resolution,[],[f82,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1) | ~spl5_2),
% 0.21/0.44    inference(resolution,[],[f38,f20])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) | ~spl5_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f36])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1) | spl5_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f80])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ~spl5_6 | ~spl5_3 | spl5_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f76,f64,f41,f80])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK1) | spl5_5),
% 0.21/0.44    inference(resolution,[],[f66,f19])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) | spl5_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ~spl5_2 | spl5_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    $false | (~spl5_2 | spl5_4)),
% 0.21/0.44    inference(resolution,[],[f62,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0) | ~spl5_2),
% 0.21/0.44    inference(resolution,[],[f38,f21])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0) | spl5_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f60])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ~spl5_4 | ~spl5_5 | spl5_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f56,f32,f64,f60])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK1,sK2)) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK0) | spl5_1),
% 0.21/0.44    inference(resolution,[],[f33,f19])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) | spl5_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f32])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f41,f36,f32])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.44    inference(resolution,[],[f23,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (sQ4_eqProxy(k3_xboole_0(X0,X1),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f18,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.44    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ~sQ4_eqProxy(k3_xboole_0(k3_xboole_0(sK0,sK1),sK2),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f12,f22])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f5])).
% 0.21/0.44  fof(f5,plain,(
% 0.21/0.44    ? [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) != k3_xboole_0(X0,k3_xboole_0(X1,X2)) => k3_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f4,plain,(
% 0.21/0.44    ? [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) != k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.44    inference(negated_conjecture,[],[f2])).
% 0.21/0.44  fof(f2,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    spl5_1 | spl5_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f29,f41,f32])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),sK2) | r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.44    inference(resolution,[],[f23,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (sQ4_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f17,f22])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl5_1 | spl5_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f28,f36,f32])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.44    inference(resolution,[],[f23,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (sQ4_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.44    inference(equality_proxy_replacement,[],[f16,f22])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (31595)------------------------------
% 0.21/0.44  % (31595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (31595)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (31595)Memory used [KB]: 6140
% 0.21/0.44  % (31595)Time elapsed: 0.063 s
% 0.21/0.44  % (31595)------------------------------
% 0.21/0.44  % (31595)------------------------------
% 0.21/0.45  % (31582)Success in time 0.096 s
%------------------------------------------------------------------------------
