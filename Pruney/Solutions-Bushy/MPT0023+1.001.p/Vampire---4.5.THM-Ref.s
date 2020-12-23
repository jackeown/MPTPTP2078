%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0023+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

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
