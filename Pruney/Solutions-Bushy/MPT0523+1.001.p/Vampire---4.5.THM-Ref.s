%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0523+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 144 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  264 ( 599 expanded)
%              Number of equality atoms :   21 (  72 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f82,f84,f90,f92,f186,f219,f225])).

fof(f225,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f214,f69,f73])).

fof(f73,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f69,plain,
    ( spl5_3
  <=> r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f214,plain,
    ( r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f71,f45])).

fof(f45,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X2),k5_relat_1(sK1,k6_relat_1(X3)))
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k8_relat_1(sK0,sK1) != k5_relat_1(sK1,k6_relat_1(sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK0,sK1) != k5_relat_1(sK1,k6_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f71,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f219,plain,
    ( ~ spl5_1
    | spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f216,f69,f78,f61])).

fof(f61,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f78,plain,
    ( spl5_5
  <=> r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f216,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f71,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f186,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | spl5_3 ),
    inference(avatar_split_clause,[],[f183,f69,f78,f73,f61])).

fof(f183,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0)
    | ~ v1_relat_1(sK1)
    | spl5_3 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f92,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f89,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f89,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_6
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f90,plain,
    ( ~ spl5_1
    | ~ spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f85,f65,f87,f61])).

fof(f65,plain,
    ( spl5_2
  <=> v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl5_2 ),
    inference(resolution,[],[f67,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f67,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f84,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f63,f21])).

fof(f63,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f82,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f59,f78,f73,f69,f65,f61])).

fof(f59,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k8_relat_1(X0,X1),X2)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK3(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
                    & r2_hidden(sK3(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f38,plain,(
    ~ sQ4_eqProxy(k8_relat_1(sK0,sK1),k5_relat_1(sK1,k6_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f22,f37])).

fof(f22,plain,(
    k8_relat_1(sK0,sK1) != k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_5 ),
    inference(avatar_split_clause,[],[f58,f78,f69,f65,f61])).

fof(f58,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)
    | r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f57,f73,f69,f65,f61])).

fof(f57,plain,
    ( r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0)
    | r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k8_relat_1(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f27,f37])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
