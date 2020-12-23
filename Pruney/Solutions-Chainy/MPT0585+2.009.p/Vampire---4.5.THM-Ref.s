%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:53 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 244 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  396 (1152 expanded)
%              Number of equality atoms :   34 ( 163 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f130,f173,f198,f382,f392,f437,f443,f885,f1359,f1365,f1379,f1427])).

fof(f1427,plain,
    ( ~ spl8_9
    | spl8_4
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f1422,f379,f99,f156])).

fof(f156,plain,
    ( spl8_9
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f99,plain,
    ( spl8_4
  <=> r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f379,plain,
    ( spl8_24
  <=> r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f1422,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl8_24 ),
    inference(resolution,[],[f380,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f380,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f379])).

fof(f1379,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_5
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f432,f95,f104,f91,f87])).

fof(f87,plain,
    ( spl8_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f91,plain,
    ( spl8_2
  <=> v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f104,plain,
    ( spl8_5
  <=> r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f95,plain,
    ( spl8_3
  <=> r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f432,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0)
    | ~ v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | ~ v1_relat_1(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f97,f45])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK2(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                    & r2_hidden(sK2(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
            & r2_hidden(sK2(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f97,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1365,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f474,f104,f99,f95,f91])).

fof(f474,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0)
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1))
    | ~ r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | ~ v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ~ sQ7_eqProxy(k7_relat_1(sK0,k1_relat_1(sK1)),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) ),
    inference(equality_proxy_replacement,[],[f29,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f29,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f64,plain,(
    ! [X17,X16] :
      ( sQ7_eqProxy(k7_relat_1(sK0,X16),X17)
      | ~ r2_hidden(k4_tarski(sK2(sK0,X16,X17),sK3(sK0,X16,X17)),sK0)
      | ~ r2_hidden(sK2(sK0,X16,X17),X16)
      | ~ r2_hidden(k4_tarski(sK2(sK0,X16,X17),sK3(sK0,X16,X17)),X17)
      | ~ v1_relat_1(X17) ) ),
    inference(resolution,[],[f27,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k7_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f35,f49])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1359,plain,
    ( ~ spl8_5
    | spl8_59 ),
    inference(avatar_contradiction_clause,[],[f1353])).

fof(f1353,plain,
    ( $false
    | ~ spl8_5
    | spl8_59 ),
    inference(resolution,[],[f884,f347])).

fof(f347,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0))
    | ~ spl8_5 ),
    inference(resolution,[],[f106,f47])).

fof(f47,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f106,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f884,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0))
    | spl8_59 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl8_59
  <=> r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f885,plain,
    ( ~ spl8_9
    | ~ spl8_59
    | ~ spl8_4
    | spl8_24 ),
    inference(avatar_split_clause,[],[f876,f379,f99,f882,f156])).

fof(f876,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl8_24 ),
    inference(resolution,[],[f381,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f381,plain,
    ( ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | spl8_24 ),
    inference(avatar_component_clause,[],[f379])).

fof(f443,plain,
    ( ~ spl8_2
    | spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f313,f99,f95,f91])).

fof(f313,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1))
    | r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | ~ v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) ),
    inference(resolution,[],[f68,f50])).

fof(f68,plain,(
    ! [X24,X25] :
      ( sQ7_eqProxy(k7_relat_1(sK0,X24),X25)
      | r2_hidden(sK2(sK0,X24,X25),X24)
      | r2_hidden(k4_tarski(sK2(sK0,X24,X25),sK3(sK0,X24,X25)),X25)
      | ~ v1_relat_1(X25) ) ),
    inference(resolution,[],[f27,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f33,f49])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f437,plain,
    ( spl8_24
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f430,f128,f95,f379])).

fof(f128,plain,
    ( spl8_6
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f430,plain,
    ( r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(resolution,[],[f97,f129])).

fof(f129,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK0,X1))
        | r2_hidden(X0,X1) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f392,plain,
    ( ~ spl8_2
    | spl8_3
    | spl8_5 ),
    inference(avatar_split_clause,[],[f355,f104,f95,f91])).

fof(f355,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0)
    | r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | ~ v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X21,X20] :
      ( sQ7_eqProxy(k7_relat_1(sK0,X20),X21)
      | r2_hidden(k4_tarski(sK2(sK0,X20,X21),sK3(sK0,X20,X21)),sK0)
      | r2_hidden(k4_tarski(sK2(sK0,X20,X21),sK3(sK0,X20,X21)),X21)
      | ~ v1_relat_1(X21) ) ),
    inference(resolution,[],[f27,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k7_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f34,f49])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f382,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_24
    | ~ spl8_5
    | spl8_3 ),
    inference(avatar_split_clause,[],[f374,f95,f104,f379,f91,f87])).

fof(f374,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0)
    | ~ r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | ~ v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | ~ v1_relat_1(sK0)
    | spl8_3 ),
    inference(resolution,[],[f96,f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f198,plain,(
    spl8_9 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl8_9 ),
    inference(resolution,[],[f158,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f158,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f156])).

fof(f173,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl8_2 ),
    inference(resolution,[],[f93,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f93,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f130,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f111,f128,f87])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK0,X1))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f89,f27])).

fof(f89,plain,
    ( ~ v1_relat_1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:52:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (6607)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (6603)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (6598)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (6600)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (6611)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (6606)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (6617)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (6605)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (6617)Refutation not found, incomplete strategy% (6617)------------------------------
% 0.21/0.50  % (6617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6617)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6617)Memory used [KB]: 10618
% 0.21/0.50  % (6617)Time elapsed: 0.087 s
% 0.21/0.50  % (6617)------------------------------
% 0.21/0.50  % (6617)------------------------------
% 0.21/0.50  % (6615)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (6616)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (6604)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (6601)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (6602)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (6598)Refutation not found, incomplete strategy% (6598)------------------------------
% 0.21/0.51  % (6598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6598)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6598)Memory used [KB]: 10490
% 0.21/0.51  % (6598)Time elapsed: 0.075 s
% 0.21/0.51  % (6598)------------------------------
% 0.21/0.51  % (6598)------------------------------
% 0.21/0.51  % (6612)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (6613)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (6599)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (6609)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6608)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (6610)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (6610)Refutation not found, incomplete strategy% (6610)------------------------------
% 0.21/0.52  % (6610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6610)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6610)Memory used [KB]: 1663
% 0.21/0.52  % (6610)Time elapsed: 0.107 s
% 0.21/0.52  % (6610)------------------------------
% 0.21/0.52  % (6610)------------------------------
% 0.21/0.52  % (6597)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (6614)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 2.09/0.63  % (6609)Refutation found. Thanks to Tanya!
% 2.09/0.63  % SZS status Theorem for theBenchmark
% 2.09/0.63  % SZS output start Proof for theBenchmark
% 2.09/0.64  fof(f1428,plain,(
% 2.09/0.64    $false),
% 2.09/0.64    inference(avatar_sat_refutation,[],[f110,f130,f173,f198,f382,f392,f437,f443,f885,f1359,f1365,f1379,f1427])).
% 2.09/0.64  fof(f1427,plain,(
% 2.09/0.64    ~spl8_9 | spl8_4 | ~spl8_24),
% 2.09/0.64    inference(avatar_split_clause,[],[f1422,f379,f99,f156])).
% 2.09/0.64  fof(f156,plain,(
% 2.09/0.64    spl8_9 <=> v1_relat_1(sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.09/0.64  fof(f99,plain,(
% 2.09/0.64    spl8_4 <=> r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.09/0.64  fof(f379,plain,(
% 2.09/0.64    spl8_24 <=> r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 2.09/0.64  fof(f1422,plain,(
% 2.09/0.64    r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl8_24),
% 2.09/0.64    inference(resolution,[],[f380,f42])).
% 2.09/0.64  fof(f42,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f26])).
% 2.20/0.64  fof(f26,plain,(
% 2.20/0.64    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.20/0.64    inference(flattening,[],[f25])).
% 2.20/0.64  fof(f25,plain,(
% 2.20/0.64    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 2.20/0.64    inference(nnf_transformation,[],[f10])).
% 2.20/0.64  fof(f10,plain,(
% 2.20/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 2.20/0.64    inference(ennf_transformation,[],[f4])).
% 2.20/0.64  fof(f4,axiom,(
% 2.20/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 2.20/0.64  fof(f380,plain,(
% 2.20/0.64    r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | ~spl8_24),
% 2.20/0.64    inference(avatar_component_clause,[],[f379])).
% 2.20/0.64  fof(f1379,plain,(
% 2.20/0.64    ~spl8_1 | ~spl8_2 | spl8_5 | ~spl8_3),
% 2.20/0.64    inference(avatar_split_clause,[],[f432,f95,f104,f91,f87])).
% 2.20/0.64  fof(f87,plain,(
% 2.20/0.64    spl8_1 <=> v1_relat_1(sK0)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.20/0.64  fof(f91,plain,(
% 2.20/0.64    spl8_2 <=> v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.20/0.64  fof(f104,plain,(
% 2.20/0.64    spl8_5 <=> r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.20/0.64  fof(f95,plain,(
% 2.20/0.64    spl8_3 <=> r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.20/0.64  fof(f432,plain,(
% 2.20/0.64    r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0) | ~v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | ~v1_relat_1(sK0) | ~spl8_3),
% 2.20/0.64    inference(resolution,[],[f97,f45])).
% 2.20/0.64  fof(f45,plain,(
% 2.20/0.64    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(equality_resolution,[],[f31])).
% 2.20/0.64  fof(f31,plain,(
% 2.20/0.64    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f18])).
% 2.20/0.64  fof(f18,plain,(
% 2.20/0.64    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) & r2_hidden(sK2(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.20/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).
% 2.20/0.64  fof(f17,plain,(
% 2.20/0.64    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) & r2_hidden(sK2(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 2.20/0.64    introduced(choice_axiom,[])).
% 2.20/0.64  fof(f16,plain,(
% 2.20/0.64    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.20/0.64    inference(rectify,[],[f15])).
% 2.20/0.64  fof(f15,plain,(
% 2.20/0.64    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.20/0.64    inference(flattening,[],[f14])).
% 2.20/0.64  fof(f14,plain,(
% 2.20/0.64    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.20/0.64    inference(nnf_transformation,[],[f8])).
% 2.20/0.64  fof(f8,plain,(
% 2.20/0.64    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.20/0.64    inference(ennf_transformation,[],[f1])).
% 2.20/0.64  fof(f1,axiom,(
% 2.20/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 2.20/0.64  fof(f97,plain,(
% 2.20/0.64    r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | ~spl8_3),
% 2.20/0.64    inference(avatar_component_clause,[],[f95])).
% 2.20/0.64  fof(f1365,plain,(
% 2.20/0.64    ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5),
% 2.20/0.64    inference(avatar_split_clause,[],[f474,f104,f99,f95,f91])).
% 2.20/0.64  fof(f474,plain,(
% 2.20/0.64    ~r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1)) | ~r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | ~v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),
% 2.20/0.64    inference(resolution,[],[f64,f50])).
% 2.20/0.64  fof(f50,plain,(
% 2.20/0.64    ~sQ7_eqProxy(k7_relat_1(sK0,k1_relat_1(sK1)),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),
% 2.20/0.64    inference(equality_proxy_replacement,[],[f29,f49])).
% 2.20/0.64  fof(f49,plain,(
% 2.20/0.64    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 2.20/0.64    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 2.20/0.64  fof(f29,plain,(
% 2.20/0.64    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 2.20/0.64    inference(cnf_transformation,[],[f13])).
% 2.20/0.64  fof(f13,plain,(
% 2.20/0.64    (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 2.20/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).
% 2.20/0.64  fof(f11,plain,(
% 2.20/0.64    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 2.20/0.64    introduced(choice_axiom,[])).
% 2.20/0.64  fof(f12,plain,(
% 2.20/0.64    ? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) => (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1))),
% 2.20/0.64    introduced(choice_axiom,[])).
% 2.20/0.64  fof(f7,plain,(
% 2.20/0.64    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.20/0.64    inference(ennf_transformation,[],[f6])).
% 2.20/0.64  fof(f6,negated_conjecture,(
% 2.20/0.64    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 2.20/0.64    inference(negated_conjecture,[],[f5])).
% 2.20/0.64  fof(f5,conjecture,(
% 2.20/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 2.20/0.64  fof(f64,plain,(
% 2.20/0.64    ( ! [X17,X16] : (sQ7_eqProxy(k7_relat_1(sK0,X16),X17) | ~r2_hidden(k4_tarski(sK2(sK0,X16,X17),sK3(sK0,X16,X17)),sK0) | ~r2_hidden(sK2(sK0,X16,X17),X16) | ~r2_hidden(k4_tarski(sK2(sK0,X16,X17),sK3(sK0,X16,X17)),X17) | ~v1_relat_1(X17)) )),
% 2.20/0.64    inference(resolution,[],[f27,f51])).
% 2.20/0.64  fof(f51,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (sQ7_eqProxy(k7_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(equality_proxy_replacement,[],[f35,f49])).
% 2.20/0.64  fof(f35,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f18])).
% 2.20/0.64  fof(f27,plain,(
% 2.20/0.64    v1_relat_1(sK0)),
% 2.20/0.64    inference(cnf_transformation,[],[f13])).
% 2.20/0.64  fof(f1359,plain,(
% 2.20/0.64    ~spl8_5 | spl8_59),
% 2.20/0.64    inference(avatar_contradiction_clause,[],[f1353])).
% 2.20/0.64  fof(f1353,plain,(
% 2.20/0.64    $false | (~spl8_5 | spl8_59)),
% 2.20/0.64    inference(resolution,[],[f884,f347])).
% 2.20/0.64  fof(f347,plain,(
% 2.20/0.64    r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0)) | ~spl8_5),
% 2.20/0.64    inference(resolution,[],[f106,f47])).
% 2.20/0.64  fof(f47,plain,(
% 2.20/0.64    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 2.20/0.64    inference(equality_resolution,[],[f38])).
% 2.20/0.64  fof(f38,plain,(
% 2.20/0.64    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 2.20/0.64    inference(cnf_transformation,[],[f24])).
% 2.20/0.64  fof(f24,plain,(
% 2.20/0.64    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.20/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f20,f23,f22,f21])).
% 2.20/0.64  fof(f21,plain,(
% 2.20/0.64    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.20/0.64    introduced(choice_axiom,[])).
% 2.20/0.64  fof(f22,plain,(
% 2.20/0.64    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 2.20/0.64    introduced(choice_axiom,[])).
% 2.20/0.64  fof(f23,plain,(
% 2.20/0.64    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 2.20/0.64    introduced(choice_axiom,[])).
% 2.20/0.64  fof(f20,plain,(
% 2.20/0.64    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 2.20/0.64    inference(rectify,[],[f19])).
% 2.20/0.64  fof(f19,plain,(
% 2.20/0.64    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 2.20/0.64    inference(nnf_transformation,[],[f2])).
% 2.20/0.64  fof(f2,axiom,(
% 2.20/0.64    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 2.20/0.64  fof(f106,plain,(
% 2.20/0.64    r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0) | ~spl8_5),
% 2.20/0.64    inference(avatar_component_clause,[],[f104])).
% 2.20/0.64  fof(f884,plain,(
% 2.20/0.64    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0)) | spl8_59),
% 2.20/0.64    inference(avatar_component_clause,[],[f882])).
% 2.20/0.64  fof(f882,plain,(
% 2.20/0.64    spl8_59 <=> r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 2.20/0.64  fof(f885,plain,(
% 2.20/0.64    ~spl8_9 | ~spl8_59 | ~spl8_4 | spl8_24),
% 2.20/0.64    inference(avatar_split_clause,[],[f876,f379,f99,f882,f156])).
% 2.20/0.64  fof(f876,plain,(
% 2.20/0.64    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1)) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK0)) | ~v1_relat_1(sK1) | spl8_24),
% 2.20/0.64    inference(resolution,[],[f381,f43])).
% 2.20/0.64  fof(f43,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f26])).
% 2.20/0.64  fof(f381,plain,(
% 2.20/0.64    ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | spl8_24),
% 2.20/0.64    inference(avatar_component_clause,[],[f379])).
% 2.20/0.64  fof(f443,plain,(
% 2.20/0.64    ~spl8_2 | spl8_3 | spl8_4),
% 2.20/0.64    inference(avatar_split_clause,[],[f313,f99,f95,f91])).
% 2.20/0.64  fof(f313,plain,(
% 2.20/0.64    r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(sK1)) | r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | ~v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),
% 2.20/0.64    inference(resolution,[],[f68,f50])).
% 2.20/0.64  fof(f68,plain,(
% 2.20/0.64    ( ! [X24,X25] : (sQ7_eqProxy(k7_relat_1(sK0,X24),X25) | r2_hidden(sK2(sK0,X24,X25),X24) | r2_hidden(k4_tarski(sK2(sK0,X24,X25),sK3(sK0,X24,X25)),X25) | ~v1_relat_1(X25)) )),
% 2.20/0.64    inference(resolution,[],[f27,f53])).
% 2.20/0.64  fof(f53,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (sQ7_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(equality_proxy_replacement,[],[f33,f49])).
% 2.20/0.64  fof(f33,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f18])).
% 2.20/0.64  fof(f437,plain,(
% 2.20/0.64    spl8_24 | ~spl8_3 | ~spl8_6),
% 2.20/0.64    inference(avatar_split_clause,[],[f430,f128,f95,f379])).
% 2.20/0.64  fof(f128,plain,(
% 2.20/0.64    spl8_6 <=> ! [X1,X0,X2] : (r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK0,X1)))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.20/0.64  fof(f430,plain,(
% 2.20/0.64    r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | (~spl8_3 | ~spl8_6)),
% 2.20/0.64    inference(resolution,[],[f97,f129])).
% 2.20/0.64  fof(f129,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK0,X1)) | r2_hidden(X0,X1)) ) | ~spl8_6),
% 2.20/0.64    inference(avatar_component_clause,[],[f128])).
% 2.20/0.64  fof(f392,plain,(
% 2.20/0.64    ~spl8_2 | spl8_3 | spl8_5),
% 2.20/0.64    inference(avatar_split_clause,[],[f355,f104,f95,f91])).
% 2.20/0.64  fof(f355,plain,(
% 2.20/0.64    r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0) | r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | ~v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),
% 2.20/0.64    inference(resolution,[],[f66,f50])).
% 2.20/0.64  fof(f66,plain,(
% 2.20/0.64    ( ! [X21,X20] : (sQ7_eqProxy(k7_relat_1(sK0,X20),X21) | r2_hidden(k4_tarski(sK2(sK0,X20,X21),sK3(sK0,X20,X21)),sK0) | r2_hidden(k4_tarski(sK2(sK0,X20,X21),sK3(sK0,X20,X21)),X21) | ~v1_relat_1(X21)) )),
% 2.20/0.64    inference(resolution,[],[f27,f52])).
% 2.20/0.64  fof(f52,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (sQ7_eqProxy(k7_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(equality_proxy_replacement,[],[f34,f49])).
% 2.20/0.64  fof(f34,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f18])).
% 2.20/0.64  fof(f382,plain,(
% 2.20/0.64    ~spl8_1 | ~spl8_2 | ~spl8_24 | ~spl8_5 | spl8_3),
% 2.20/0.64    inference(avatar_split_clause,[],[f374,f95,f104,f379,f91,f87])).
% 2.20/0.64  fof(f374,plain,(
% 2.20/0.64    ~r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),sK0) | ~r2_hidden(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | ~v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | ~v1_relat_1(sK0) | spl8_3),
% 2.20/0.64    inference(resolution,[],[f96,f44])).
% 2.20/0.64  fof(f44,plain,(
% 2.20/0.64    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(equality_resolution,[],[f32])).
% 2.20/0.64  fof(f32,plain,(
% 2.20/0.64    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f18])).
% 2.20/0.64  fof(f96,plain,(
% 2.20/0.64    ~r2_hidden(k4_tarski(sK2(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),sK3(sK0,k1_relat_1(sK1),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))))),k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | spl8_3),
% 2.20/0.64    inference(avatar_component_clause,[],[f95])).
% 2.20/0.64  fof(f198,plain,(
% 2.20/0.64    spl8_9),
% 2.20/0.64    inference(avatar_contradiction_clause,[],[f197])).
% 2.20/0.64  fof(f197,plain,(
% 2.20/0.64    $false | spl8_9),
% 2.20/0.64    inference(resolution,[],[f158,f28])).
% 2.20/0.64  fof(f28,plain,(
% 2.20/0.64    v1_relat_1(sK1)),
% 2.20/0.64    inference(cnf_transformation,[],[f13])).
% 2.20/0.64  fof(f158,plain,(
% 2.20/0.64    ~v1_relat_1(sK1) | spl8_9),
% 2.20/0.64    inference(avatar_component_clause,[],[f156])).
% 2.20/0.64  fof(f173,plain,(
% 2.20/0.64    spl8_2),
% 2.20/0.64    inference(avatar_contradiction_clause,[],[f171])).
% 2.20/0.64  fof(f171,plain,(
% 2.20/0.64    $false | spl8_2),
% 2.20/0.64    inference(resolution,[],[f93,f57])).
% 2.20/0.64  fof(f57,plain,(
% 2.20/0.64    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) )),
% 2.20/0.64    inference(resolution,[],[f27,f36])).
% 2.20/0.64  fof(f36,plain,(
% 2.20/0.64    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f9])).
% 2.20/0.64  fof(f9,plain,(
% 2.20/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.20/0.64    inference(ennf_transformation,[],[f3])).
% 2.20/0.64  fof(f3,axiom,(
% 2.20/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.20/0.64  fof(f93,plain,(
% 2.20/0.64    ~v1_relat_1(k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))) | spl8_2),
% 2.20/0.64    inference(avatar_component_clause,[],[f91])).
% 2.20/0.64  fof(f130,plain,(
% 2.20/0.64    ~spl8_1 | spl8_6),
% 2.20/0.64    inference(avatar_split_clause,[],[f111,f128,f87])).
% 2.20/0.64  fof(f111,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(k4_tarski(X0,X2),k7_relat_1(sK0,X1)) | ~v1_relat_1(sK0)) )),
% 2.20/0.64    inference(resolution,[],[f57,f46])).
% 2.20/0.64  fof(f46,plain,(
% 2.20/0.64    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(equality_resolution,[],[f30])).
% 2.20/0.64  fof(f30,plain,(
% 2.20/0.64    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f18])).
% 2.20/0.64  fof(f110,plain,(
% 2.20/0.64    spl8_1),
% 2.20/0.64    inference(avatar_contradiction_clause,[],[f109])).
% 2.20/0.64  fof(f109,plain,(
% 2.20/0.64    $false | spl8_1),
% 2.20/0.64    inference(resolution,[],[f89,f27])).
% 2.20/0.64  fof(f89,plain,(
% 2.20/0.64    ~v1_relat_1(sK0) | spl8_1),
% 2.20/0.64    inference(avatar_component_clause,[],[f87])).
% 2.20/0.64  % SZS output end Proof for theBenchmark
% 2.20/0.64  % (6609)------------------------------
% 2.20/0.64  % (6609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.64  % (6609)Termination reason: Refutation
% 2.20/0.64  
% 2.20/0.64  % (6609)Memory used [KB]: 7547
% 2.20/0.64  % (6609)Time elapsed: 0.214 s
% 2.20/0.64  % (6609)------------------------------
% 2.20/0.64  % (6609)------------------------------
% 2.20/0.64  % (6596)Success in time 0.277 s
%------------------------------------------------------------------------------
