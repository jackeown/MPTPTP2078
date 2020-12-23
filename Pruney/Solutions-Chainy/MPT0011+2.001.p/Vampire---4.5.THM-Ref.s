%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 198 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 (1189 expanded)
%              Number of equality atoms :   23 ( 157 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f44,f45,f61,f67,f76,f82,f92,f99,f105,f106])).

fof(f106,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f73,f32,f40])).

fof(f40,plain,
    ( spl5_3
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f32,plain,
    ( spl5_1
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f73,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | spl5_1 ),
    inference(resolution,[],[f64,f19])).

fof(f19,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f10])).

fof(f10,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f8])).

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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f64,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | spl5_1 ),
    inference(resolution,[],[f33,f19])).

fof(f33,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f105,plain,
    ( spl5_5
    | spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f95,f89,f40,f58])).

fof(f58,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f89,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f95,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f91,f21])).

fof(f21,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f99,plain,
    ( ~ spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f78,f36,f54])).

fof(f54,plain,
    ( spl5_4
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f36,plain,
    ( spl5_2
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f78,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl5_2 ),
    inference(resolution,[],[f37,f20])).

fof(f20,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f92,plain,
    ( spl5_4
    | spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f85,f32,f89,f54])).

fof(f85,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f34,f21])).

fof(f34,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f82,plain,
    ( ~ spl5_5
    | spl5_2 ),
    inference(avatar_split_clause,[],[f79,f36,f58])).

fof(f79,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | spl5_2 ),
    inference(resolution,[],[f37,f19])).

fof(f76,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f72,f32,f58])).

fof(f72,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | spl5_1 ),
    inference(resolution,[],[f64,f20])).

fof(f67,plain,
    ( ~ spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f63,f32,f54])).

fof(f63,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | spl5_1 ),
    inference(resolution,[],[f33,f20])).

fof(f61,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f50,f36,f58,f54])).

fof(f50,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f21])).

fof(f38,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f45,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f30,f40,f32])).

fof(f30,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f18,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ~ sQ4_eqProxy(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f12,f22])).

fof(f12,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2))
   => k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f44,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f29,f36,f32])).

fof(f29,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f23,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f17,f22])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,
    ( spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f28,f40,f36,f32])).

fof(f28,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f16,f22])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.45  % (12375)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.46  % (12368)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.46  % (12362)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.46  % (12360)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (12368)Refutation not found, incomplete strategy% (12368)------------------------------
% 0.22/0.47  % (12368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12368)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (12368)Memory used [KB]: 6012
% 0.22/0.47  % (12368)Time elapsed: 0.065 s
% 0.22/0.47  % (12368)------------------------------
% 0.22/0.47  % (12368)------------------------------
% 0.22/0.48  % (12371)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (12363)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (12371)Refutation not found, incomplete strategy% (12371)------------------------------
% 0.22/0.49  % (12371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12371)Memory used [KB]: 1535
% 0.22/0.49  % (12371)Time elapsed: 0.082 s
% 0.22/0.49  % (12371)------------------------------
% 0.22/0.49  % (12371)------------------------------
% 0.22/0.49  % (12367)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (12372)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (12372)Refutation not found, incomplete strategy% (12372)------------------------------
% 0.22/0.50  % (12372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12372)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12372)Memory used [KB]: 10618
% 0.22/0.50  % (12372)Time elapsed: 0.049 s
% 0.22/0.50  % (12372)------------------------------
% 0.22/0.50  % (12372)------------------------------
% 0.22/0.50  % (12370)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12378)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (12370)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f43,f44,f45,f61,f67,f76,f82,f92,f99,f105,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ~spl5_3 | spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f73,f32,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    spl5_3 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    spl5_1 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | spl5_1),
% 0.22/0.50    inference(resolution,[],[f64,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(rectify,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(flattening,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) | spl5_1),
% 0.22/0.50    inference(resolution,[],[f33,f19])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f32])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl5_5 | spl5_3 | ~spl5_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f95,f89,f40,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl5_5 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl5_6 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | ~spl5_6),
% 0.22/0.50    inference(resolution,[],[f91,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) | ~spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~spl5_4 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f78,f36,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl5_4 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    spl5_2 <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | spl5_2),
% 0.22/0.50    inference(resolution,[],[f37,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) | spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f36])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl5_4 | spl5_6 | ~spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f85,f32,f89,f54])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | ~spl5_1),
% 0.22/0.50    inference(resolution,[],[f34,f21])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f32])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~spl5_5 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f79,f36,f58])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | spl5_2),
% 0.22/0.50    inference(resolution,[],[f37,f19])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ~spl5_5 | spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f72,f32,f58])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | spl5_1),
% 0.22/0.50    inference(resolution,[],[f64,f20])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ~spl5_4 | spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f32,f54])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | spl5_1),
% 0.22/0.50    inference(resolution,[],[f33,f20])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl5_4 | spl5_5 | ~spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f36,f58,f54])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) | ~spl5_2),
% 0.22/0.50    inference(resolution,[],[f38,f21])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f36])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f40,f32])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.50    inference(resolution,[],[f23,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (sQ4_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(equality_proxy_replacement,[],[f18,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ~sQ4_eqProxy(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.50    inference(equality_proxy_replacement,[],[f12,f22])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f4,f5])).
% 0.22/0.50  fof(f5,plain,(
% 0.22/0.50    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2)) => k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f4,plain,(
% 0.22/0.50    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.50    inference(negated_conjecture,[],[f2])).
% 0.22/0.50  fof(f2,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f36,f32])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.50    inference(resolution,[],[f23,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (sQ4_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(equality_proxy_replacement,[],[f17,f22])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl5_1 | spl5_2 | spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f40,f36,f32])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.50    inference(resolution,[],[f23,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (sQ4_eqProxy(k2_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(equality_proxy_replacement,[],[f16,f22])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (12370)------------------------------
% 0.22/0.50  % (12370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12370)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (12370)Memory used [KB]: 6140
% 0.22/0.50  % (12370)Time elapsed: 0.100 s
% 0.22/0.50  % (12370)------------------------------
% 0.22/0.50  % (12370)------------------------------
% 0.22/0.50  % (12378)Refutation not found, incomplete strategy% (12378)------------------------------
% 0.22/0.50  % (12378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12378)Memory used [KB]: 10490
% 0.22/0.50  % (12378)Time elapsed: 0.092 s
% 0.22/0.50  % (12378)------------------------------
% 0.22/0.50  % (12378)------------------------------
% 0.22/0.50  % (12359)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12377)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (12359)Refutation not found, incomplete strategy% (12359)------------------------------
% 0.22/0.50  % (12359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12359)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12359)Memory used [KB]: 10490
% 0.22/0.50  % (12359)Time elapsed: 0.092 s
% 0.22/0.50  % (12359)------------------------------
% 0.22/0.50  % (12359)------------------------------
% 0.22/0.51  % (12376)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (12361)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (12365)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (12361)Refutation not found, incomplete strategy% (12361)------------------------------
% 0.22/0.51  % (12361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12361)Memory used [KB]: 10490
% 0.22/0.51  % (12361)Time elapsed: 0.091 s
% 0.22/0.51  % (12361)------------------------------
% 0.22/0.51  % (12361)------------------------------
% 0.22/0.51  % (12366)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (12369)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (12369)Refutation not found, incomplete strategy% (12369)------------------------------
% 0.22/0.51  % (12369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12369)Memory used [KB]: 10490
% 0.22/0.51  % (12369)Time elapsed: 0.102 s
% 0.22/0.51  % (12369)------------------------------
% 0.22/0.51  % (12369)------------------------------
% 0.22/0.51  % (12364)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (12357)Success in time 0.158 s
%------------------------------------------------------------------------------
