%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (3239)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (3230)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (3223)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (3226)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (3243)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (3226)Refutation not found, incomplete strategy% (3226)------------------------------
% 0.20/0.48  % (3226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3226)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (3226)Memory used [KB]: 10490
% 0.20/0.48  % (3226)Time elapsed: 0.070 s
% 0.20/0.48  % (3226)------------------------------
% 0.20/0.48  % (3226)------------------------------
% 0.20/0.48  % (3231)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (3235)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (3224)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (3227)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (3224)Refutation not found, incomplete strategy% (3224)------------------------------
% 0.20/0.49  % (3224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3224)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3224)Memory used [KB]: 10490
% 0.20/0.49  % (3224)Time elapsed: 0.082 s
% 0.20/0.49  % (3224)------------------------------
% 0.20/0.49  % (3224)------------------------------
% 0.20/0.50  % (3237)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (3237)Refutation not found, incomplete strategy% (3237)------------------------------
% 0.20/0.50  % (3237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3237)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3237)Memory used [KB]: 1535
% 0.20/0.50  % (3237)Time elapsed: 0.081 s
% 0.20/0.50  % (3237)------------------------------
% 0.20/0.50  % (3237)------------------------------
% 0.20/0.50  % (3228)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (3225)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (3238)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (3233)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (3232)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (3241)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (3240)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (3235)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f76,f81,f82,f84,f90,f92,f186,f219,f225])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    spl5_4 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f214,f69,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl5_4 <=> r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl5_3 <=> r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f214,plain,(
% 0.20/0.51    r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f71,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(X4,X2),k5_relat_1(sK1,k6_relat_1(X3))) | r2_hidden(X2,X3)) )),
% 0.20/0.51    inference(resolution,[],[f21,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X2) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~v1_relat_1(X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 0.20/0.51    inference(nnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    k8_relat_1(sK0,sK1) != k5_relat_1(sK1,k6_relat_1(sK0)) & v1_relat_1(sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1] : (k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0)) & v1_relat_1(X1)) => (k8_relat_1(sK0,sK1) != k5_relat_1(sK1,k6_relat_1(sK0)) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f7,plain,(
% 0.20/0.51    ? [X0,X1] : (k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0)) & v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f5])).
% 0.20/0.51  fof(f5,conjecture,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ~spl5_1 | spl5_5 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f216,f69,f78,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl5_1 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl5_5 <=> r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~v1_relat_1(sK1) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f71,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~v1_relat_1(X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ~spl5_1 | ~spl5_4 | ~spl5_5 | spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f183,f69,f78,f73,f61])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0) | ~v1_relat_1(sK1) | spl5_3),
% 0.20/0.51    inference(resolution,[],[f70,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2) | ~v1_relat_1(X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f69])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl5_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    $false | spl5_6),
% 0.20/0.51    inference(resolution,[],[f89,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~v1_relat_1(k6_relat_1(sK0)) | spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    spl5_6 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ~spl5_1 | ~spl5_6 | spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f85,f65,f87,f61])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    spl5_2 <=> v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK1) | spl5_2),
% 0.20/0.51    inference(resolution,[],[f67,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f65])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    $false | spl5_1),
% 0.20/0.51    inference(resolution,[],[f63,f21])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ~v1_relat_1(sK1) | spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f61])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f78,f73,f69,f65,f61])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ~r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | ~r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0) | ~r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(sK1)),
% 0.20/0.51    inference(resolution,[],[f38,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sQ4_eqProxy(k8_relat_1(X0,X1),X2) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f29,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(rectify,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ~sQ4_eqProxy(k8_relat_1(sK0,sK1),k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f22,f37])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    k8_relat_1(sK0,sK1) != k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ~spl5_1 | ~spl5_2 | spl5_3 | spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f58,f78,f69,f65,f61])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),sK1) | r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(sK1)),
% 0.20/0.51    inference(resolution,[],[f38,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sQ4_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f28,f37])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ~spl5_1 | ~spl5_2 | spl5_3 | spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f57,f73,f69,f65,f61])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    r2_hidden(sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK0) | r2_hidden(k4_tarski(sK2(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0))),sK3(sK0,sK1,k5_relat_1(sK1,k6_relat_1(sK0)))),k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) | ~v1_relat_1(sK1)),
% 0.20/0.51    inference(resolution,[],[f38,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sQ4_eqProxy(k8_relat_1(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(equality_proxy_replacement,[],[f27,f37])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k8_relat_1(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3235)------------------------------
% 0.20/0.51  % (3235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3235)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3235)Memory used [KB]: 6268
% 0.20/0.51  % (3235)Time elapsed: 0.099 s
% 0.20/0.51  % (3235)------------------------------
% 0.20/0.51  % (3235)------------------------------
% 0.20/0.51  % (3229)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (3220)Success in time 0.155 s
%------------------------------------------------------------------------------
