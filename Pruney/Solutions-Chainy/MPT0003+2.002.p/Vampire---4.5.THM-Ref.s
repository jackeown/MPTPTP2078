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
% DateTime   : Thu Dec  3 12:29:30 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 133 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  265 ( 569 expanded)
%              Number of equality atoms :   18 (  51 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f128,f150,f165,f382])).

fof(f382,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f379,f166])).

fof(f166,plain,
    ( sQ4_eqProxy(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_1 ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | sQ4_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f28,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f55,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f379,plain,
    ( ~ sQ4_eqProxy(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f369,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f39])).

fof(f369,plain,
    ( ~ sQ4_eqProxy(k1_xboole_0,k3_xboole_0(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f201,f26])).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ sQ4_eqProxy(X0,k3_xboole_0(sK0,sK1)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f200,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f39])).

fof(f200,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f184,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f184,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f168,f60])).

fof(f60,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | r2_hidden(sK2,k3_xboole_0(X0,sK1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f167,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f167,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f22,f55])).

fof(f22,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( r1_xboole_0(sK0,sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK2,sK0) )
    | ( ! [X3] :
          ( ~ r2_hidden(X3,sK1)
          | ~ r2_hidden(X3,sK0) )
      & ~ r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
        | ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK0,sK1)
        & ? [X2] :
            ( r2_hidden(X2,sK1)
            & r2_hidden(X2,sK0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK0) )
        & ~ r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( r2_hidden(X2,sK1)
        & r2_hidden(X2,sK0) )
   => ( r2_hidden(sK2,sK1)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X2] :
                ~ ( r2_hidden(X2,X1)
                  & r2_hidden(X2,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f165,plain,
    ( spl5_1
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f71,f126,f155,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f33,f39])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f155,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK0)
    | spl5_1
    | ~ spl5_3 ),
    inference(resolution,[],[f151,f123])).

fof(f123,plain,
    ( r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_3
  <=> r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f151,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK0) )
    | spl5_1 ),
    inference(subsumption_resolution,[],[f25,f56])).

fof(f56,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f25,plain,(
    ! [X3] :
      ( r1_xboole_0(sK0,sK1)
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f71,plain,
    ( ~ sQ4_eqProxy(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | spl5_1 ),
    inference(resolution,[],[f67,f50])).

fof(f50,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f39])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(k3_xboole_0(sK0,sK1),X0)
        | ~ sQ4_eqProxy(X0,k1_xboole_0) )
    | spl5_1 ),
    inference(resolution,[],[f65,f56])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ sQ4_eqProxy(k3_xboole_0(X1,X2),X0)
      | ~ sQ4_eqProxy(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0)
      | r1_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f29,f39])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(X0,X2)
      | ~ sQ4_eqProxy(X1,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f39])).

fof(f150,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f147,f26])).

fof(f147,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(resolution,[],[f127,f27])).

fof(f127,plain,
    ( r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f128,plain,
    ( spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f100,f54,f125,f121])).

fof(f100,plain,
    ( r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK1)
    | spl5_1 ),
    inference(resolution,[],[f69,f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0)
      | r2_hidden(sK3(X0,X1,k1_xboole_0),X1) ) ),
    inference(resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f34,f39])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f20,f58,f54])).

fof(f20,plain,
    ( r2_hidden(sK2,sK0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (24685)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (24677)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (24673)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (24673)Refutation not found, incomplete strategy% (24673)------------------------------
% 0.21/0.49  % (24673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (24673)Memory used [KB]: 10618
% 0.21/0.49  % (24673)Time elapsed: 0.070 s
% 0.21/0.49  % (24673)------------------------------
% 0.21/0.49  % (24673)------------------------------
% 0.21/0.50  % (24674)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (24679)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (24671)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24676)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (24675)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (24687)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (24689)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (24688)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (24686)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (24684)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (24683)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (24670)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.28/0.52  % (24670)Refutation not found, incomplete strategy% (24670)------------------------------
% 1.28/0.52  % (24670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (24670)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (24670)Memory used [KB]: 6140
% 1.28/0.52  % (24670)Time elapsed: 0.098 s
% 1.28/0.52  % (24670)------------------------------
% 1.28/0.52  % (24670)------------------------------
% 1.28/0.52  % (24675)Refutation found. Thanks to Tanya!
% 1.28/0.52  % SZS status Theorem for theBenchmark
% 1.28/0.52  % SZS output start Proof for theBenchmark
% 1.28/0.52  fof(f383,plain,(
% 1.28/0.52    $false),
% 1.28/0.52    inference(avatar_sat_refutation,[],[f61,f128,f150,f165,f382])).
% 1.28/0.52  fof(f382,plain,(
% 1.28/0.52    ~spl5_1 | ~spl5_2),
% 1.28/0.52    inference(avatar_contradiction_clause,[],[f381])).
% 1.28/0.52  fof(f381,plain,(
% 1.28/0.52    $false | (~spl5_1 | ~spl5_2)),
% 1.28/0.52    inference(subsumption_resolution,[],[f379,f166])).
% 1.28/0.52  fof(f166,plain,(
% 1.28/0.52    sQ4_eqProxy(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_1),
% 1.28/0.52    inference(resolution,[],[f55,f41])).
% 1.28/0.52  fof(f41,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | sQ4_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 1.28/0.52    inference(equality_proxy_replacement,[],[f28,f39])).
% 1.28/0.52  fof(f39,plain,(
% 1.28/0.52    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 1.28/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 1.28/0.52  fof(f28,plain,(
% 1.28/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f14])).
% 1.28/0.52  fof(f14,plain,(
% 1.28/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.28/0.52    inference(nnf_transformation,[],[f3])).
% 1.28/0.52  fof(f3,axiom,(
% 1.28/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.28/0.52  fof(f55,plain,(
% 1.28/0.52    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 1.28/0.52    inference(avatar_component_clause,[],[f54])).
% 1.28/0.52  fof(f54,plain,(
% 1.28/0.52    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.28/0.52  fof(f379,plain,(
% 1.28/0.52    ~sQ4_eqProxy(k3_xboole_0(sK0,sK1),k1_xboole_0) | (~spl5_1 | ~spl5_2)),
% 1.28/0.52    inference(resolution,[],[f369,f51])).
% 1.28/0.52  fof(f51,plain,(
% 1.28/0.52    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 1.28/0.52    inference(equality_proxy_axiom,[],[f39])).
% 1.28/0.52  fof(f369,plain,(
% 1.28/0.52    ~sQ4_eqProxy(k1_xboole_0,k3_xboole_0(sK0,sK1)) | (~spl5_1 | ~spl5_2)),
% 1.28/0.52    inference(resolution,[],[f201,f26])).
% 1.28/0.52  fof(f26,plain,(
% 1.28/0.52    v1_xboole_0(k1_xboole_0)),
% 1.28/0.52    inference(cnf_transformation,[],[f4])).
% 1.28/0.52  fof(f4,axiom,(
% 1.28/0.52    v1_xboole_0(k1_xboole_0)),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.28/0.52  fof(f201,plain,(
% 1.28/0.52    ( ! [X0] : (~v1_xboole_0(X0) | ~sQ4_eqProxy(X0,k3_xboole_0(sK0,sK1))) ) | (~spl5_1 | ~spl5_2)),
% 1.28/0.52    inference(resolution,[],[f200,f47])).
% 1.28/0.52  fof(f47,plain,(
% 1.28/0.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_xboole_0(X0) | ~sQ4_eqProxy(X0,X1)) )),
% 1.28/0.52    inference(equality_proxy_axiom,[],[f39])).
% 1.28/0.52  fof(f200,plain,(
% 1.28/0.52    ~v1_xboole_0(k3_xboole_0(sK0,sK1)) | (~spl5_1 | ~spl5_2)),
% 1.28/0.52    inference(resolution,[],[f184,f27])).
% 1.28/0.52  fof(f27,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f10])).
% 1.28/0.52  fof(f10,plain,(
% 1.28/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.28/0.52    inference(ennf_transformation,[],[f8])).
% 1.28/0.52  fof(f8,plain,(
% 1.28/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.28/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 1.28/0.52  fof(f1,axiom,(
% 1.28/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.28/0.52  fof(f184,plain,(
% 1.28/0.52    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | (~spl5_1 | ~spl5_2)),
% 1.28/0.52    inference(resolution,[],[f168,f60])).
% 1.28/0.52  fof(f60,plain,(
% 1.28/0.52    r2_hidden(sK2,sK0) | ~spl5_2),
% 1.28/0.52    inference(avatar_component_clause,[],[f58])).
% 1.28/0.52  fof(f58,plain,(
% 1.28/0.52    spl5_2 <=> r2_hidden(sK2,sK0)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.28/0.52  fof(f168,plain,(
% 1.28/0.52    ( ! [X0] : (~r2_hidden(sK2,X0) | r2_hidden(sK2,k3_xboole_0(X0,sK1))) ) | ~spl5_1),
% 1.28/0.52    inference(resolution,[],[f167,f36])).
% 1.28/0.52  fof(f36,plain,(
% 1.28/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.28/0.52    inference(equality_resolution,[],[f32])).
% 1.28/0.52  fof(f32,plain,(
% 1.28/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.28/0.52    inference(cnf_transformation,[],[f19])).
% 1.28/0.52  fof(f19,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.28/0.52  fof(f18,plain,(
% 1.28/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f17,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(rectify,[],[f16])).
% 1.28/0.52  fof(f16,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(flattening,[],[f15])).
% 1.28/0.52  fof(f15,plain,(
% 1.28/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.28/0.52    inference(nnf_transformation,[],[f2])).
% 1.28/0.52  fof(f2,axiom,(
% 1.28/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.28/0.52  fof(f167,plain,(
% 1.28/0.52    r2_hidden(sK2,sK1) | ~spl5_1),
% 1.28/0.52    inference(subsumption_resolution,[],[f22,f55])).
% 1.28/0.52  fof(f22,plain,(
% 1.28/0.52    r2_hidden(sK2,sK1) | ~r1_xboole_0(sK0,sK1)),
% 1.28/0.52    inference(cnf_transformation,[],[f13])).
% 1.28/0.52  fof(f13,plain,(
% 1.28/0.52    (r1_xboole_0(sK0,sK1) & (r2_hidden(sK2,sK1) & r2_hidden(sK2,sK0))) | (! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK0)) & ~r1_xboole_0(sK0,sK1))),
% 1.28/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).
% 1.28/0.52  fof(f11,plain,(
% 1.28/0.52    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) | (! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1))) => ((r1_xboole_0(sK0,sK1) & ? [X2] : (r2_hidden(X2,sK1) & r2_hidden(X2,sK0))) | (! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK0)) & ~r1_xboole_0(sK0,sK1)))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f12,plain,(
% 1.28/0.52    ? [X2] : (r2_hidden(X2,sK1) & r2_hidden(X2,sK0)) => (r2_hidden(sK2,sK1) & r2_hidden(sK2,sK0))),
% 1.28/0.52    introduced(choice_axiom,[])).
% 1.28/0.52  fof(f9,plain,(
% 1.28/0.52    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) | (! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.28/0.52    inference(ennf_transformation,[],[f7])).
% 1.28/0.52  fof(f7,plain,(
% 1.28/0.52    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.28/0.52    inference(rectify,[],[f6])).
% 1.28/0.52  fof(f6,negated_conjecture,(
% 1.28/0.52    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.28/0.52    inference(negated_conjecture,[],[f5])).
% 1.28/0.52  fof(f5,conjecture,(
% 1.28/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.28/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.28/0.52  fof(f165,plain,(
% 1.28/0.52    spl5_1 | ~spl5_3 | spl5_4),
% 1.28/0.52    inference(avatar_contradiction_clause,[],[f163])).
% 1.28/0.52  fof(f163,plain,(
% 1.28/0.52    $false | (spl5_1 | ~spl5_3 | spl5_4)),
% 1.28/0.52    inference(unit_resulting_resolution,[],[f71,f126,f155,f44])).
% 1.28/0.52  fof(f44,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (sQ4_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.28/0.52    inference(equality_proxy_replacement,[],[f33,f39])).
% 1.28/0.52  fof(f33,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f19])).
% 1.28/0.52  fof(f155,plain,(
% 1.28/0.52    ~r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK0) | (spl5_1 | ~spl5_3)),
% 1.28/0.52    inference(resolution,[],[f151,f123])).
% 1.28/0.52  fof(f123,plain,(
% 1.28/0.52    r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK1) | ~spl5_3),
% 1.28/0.52    inference(avatar_component_clause,[],[f121])).
% 1.28/0.52  fof(f121,plain,(
% 1.28/0.52    spl5_3 <=> r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK1)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.28/0.52  fof(f151,plain,(
% 1.28/0.52    ( ! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK0)) ) | spl5_1),
% 1.28/0.52    inference(subsumption_resolution,[],[f25,f56])).
% 1.28/0.52  fof(f56,plain,(
% 1.28/0.52    ~r1_xboole_0(sK0,sK1) | spl5_1),
% 1.28/0.52    inference(avatar_component_clause,[],[f54])).
% 1.28/0.52  fof(f25,plain,(
% 1.28/0.52    ( ! [X3] : (r1_xboole_0(sK0,sK1) | ~r2_hidden(X3,sK1) | ~r2_hidden(X3,sK0)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f13])).
% 1.28/0.52  fof(f126,plain,(
% 1.28/0.52    ~r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0) | spl5_4),
% 1.28/0.52    inference(avatar_component_clause,[],[f125])).
% 1.28/0.52  fof(f125,plain,(
% 1.28/0.52    spl5_4 <=> r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0)),
% 1.28/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.28/0.52  fof(f71,plain,(
% 1.28/0.52    ~sQ4_eqProxy(k3_xboole_0(sK0,sK1),k1_xboole_0) | spl5_1),
% 1.28/0.52    inference(resolution,[],[f67,f50])).
% 1.28/0.52  fof(f50,plain,(
% 1.28/0.52    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 1.28/0.52    inference(equality_proxy_axiom,[],[f39])).
% 1.28/0.52  fof(f67,plain,(
% 1.28/0.52    ( ! [X0] : (~sQ4_eqProxy(k3_xboole_0(sK0,sK1),X0) | ~sQ4_eqProxy(X0,k1_xboole_0)) ) | spl5_1),
% 1.28/0.52    inference(resolution,[],[f65,f56])).
% 1.28/0.52  fof(f65,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X1,X2) | ~sQ4_eqProxy(k3_xboole_0(X1,X2),X0) | ~sQ4_eqProxy(X0,k1_xboole_0)) )),
% 1.28/0.52    inference(resolution,[],[f52,f40])).
% 1.28/0.52  fof(f40,plain,(
% 1.28/0.52    ( ! [X0,X1] : (~sQ4_eqProxy(k3_xboole_0(X0,X1),k1_xboole_0) | r1_xboole_0(X0,X1)) )),
% 1.28/0.52    inference(equality_proxy_replacement,[],[f29,f39])).
% 1.28/0.52  fof(f29,plain,(
% 1.28/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.28/0.52    inference(cnf_transformation,[],[f14])).
% 1.28/0.52  fof(f52,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (sQ4_eqProxy(X0,X2) | ~sQ4_eqProxy(X1,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 1.28/0.52    inference(equality_proxy_axiom,[],[f39])).
% 1.28/0.52  fof(f150,plain,(
% 1.28/0.52    ~spl5_4),
% 1.28/0.52    inference(avatar_contradiction_clause,[],[f149])).
% 1.28/0.52  fof(f149,plain,(
% 1.28/0.52    $false | ~spl5_4),
% 1.28/0.52    inference(subsumption_resolution,[],[f147,f26])).
% 1.28/0.52  fof(f147,plain,(
% 1.28/0.52    ~v1_xboole_0(k1_xboole_0) | ~spl5_4),
% 1.28/0.52    inference(resolution,[],[f127,f27])).
% 1.28/0.52  fof(f127,plain,(
% 1.28/0.52    r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0) | ~spl5_4),
% 1.28/0.52    inference(avatar_component_clause,[],[f125])).
% 1.28/0.52  fof(f128,plain,(
% 1.28/0.52    spl5_3 | spl5_4 | spl5_1),
% 1.28/0.52    inference(avatar_split_clause,[],[f100,f54,f125,f121])).
% 1.28/0.52  fof(f100,plain,(
% 1.28/0.52    r2_hidden(sK3(sK0,sK1,k1_xboole_0),k1_xboole_0) | r2_hidden(sK3(sK0,sK1,k1_xboole_0),sK1) | spl5_1),
% 1.28/0.52    inference(resolution,[],[f69,f56])).
% 1.28/0.52  fof(f69,plain,(
% 1.28/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1,k1_xboole_0),k1_xboole_0) | r2_hidden(sK3(X0,X1,k1_xboole_0),X1)) )),
% 1.28/0.52    inference(resolution,[],[f43,f40])).
% 1.28/0.52  fof(f43,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (sQ4_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.28/0.52    inference(equality_proxy_replacement,[],[f34,f39])).
% 1.28/0.52  fof(f34,plain,(
% 1.28/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.28/0.52    inference(cnf_transformation,[],[f19])).
% 1.28/0.52  fof(f61,plain,(
% 1.28/0.52    ~spl5_1 | spl5_2),
% 1.28/0.52    inference(avatar_split_clause,[],[f20,f58,f54])).
% 1.28/0.52  fof(f20,plain,(
% 1.28/0.52    r2_hidden(sK2,sK0) | ~r1_xboole_0(sK0,sK1)),
% 1.28/0.52    inference(cnf_transformation,[],[f13])).
% 1.28/0.52  % SZS output end Proof for theBenchmark
% 1.28/0.52  % (24675)------------------------------
% 1.28/0.52  % (24675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (24675)Termination reason: Refutation
% 1.28/0.52  
% 1.28/0.52  % (24675)Memory used [KB]: 6268
% 1.28/0.52  % (24675)Time elapsed: 0.097 s
% 1.28/0.52  % (24675)------------------------------
% 1.28/0.52  % (24675)------------------------------
% 1.28/0.52  % (24669)Success in time 0.157 s
%------------------------------------------------------------------------------
