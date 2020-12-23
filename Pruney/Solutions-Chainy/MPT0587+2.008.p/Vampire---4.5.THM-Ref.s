%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  94 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  215 ( 317 expanded)
%              Number of equality atoms :   27 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f105,f136,f194,f320,f347])).

fof(f347,plain,
    ( ~ spl5_6
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f340,f101,f97,f116])).

% (2445)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f116,plain,
    ( spl5_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f97,plain,
    ( spl5_4
  <=> r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f101,plain,
    ( spl5_5
  <=> r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f340,plain,
    ( r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f103,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f103,plain,
    ( r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f320,plain,
    ( ~ spl5_4
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl5_4
    | spl5_11 ),
    inference(resolution,[],[f193,f148])).

fof(f148,plain,
    ( r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f99,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f99,plain,
    ( r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f193,plain,
    ( ~ r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_11
  <=> r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f194,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | ~ spl5_11
    | spl5_5 ),
    inference(avatar_split_clause,[],[f185,f101,f191,f97,f116])).

fof(f185,plain,
    ( ~ r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0))
    | ~ v1_relat_1(sK1)
    | spl5_5 ),
    inference(resolution,[],[f102,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,
    ( ~ r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f136,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f118,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f105,plain,
    ( ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f80,f101,f97])).

fof(f80,plain,
    ( ~ r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))
    | ~ r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f54,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f32,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f54,plain,(
    ~ sQ4_eqProxy(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) ),
    inference(equality_proxy_replacement,[],[f26,f53])).

fof(f26,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f104,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f79,f101,f97])).

fof(f79,plain,
    ( r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))
    | r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f54,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f31,f53])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (2455)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (2447)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (2437)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2432)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (2435)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (2436)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (2434)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2439)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (2453)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (2447)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f104,f105,f136,f194,f320,f347])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    ~spl5_6 | spl5_4 | ~spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f340,f101,f97,f116])).
% 0.21/0.53  % (2445)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl5_6 <=> v1_relat_1(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl5_4 <=> r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl5_5 <=> r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0)) | ~v1_relat_1(sK1) | ~spl5_5),
% 0.21/0.53    inference(resolution,[],[f103,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) | ~spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    ~spl5_4 | spl5_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f314])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    $false | (~spl5_4 | spl5_11)),
% 0.21/0.53    inference(resolution,[],[f193,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1)) | ~spl5_4),
% 0.21/0.53    inference(resolution,[],[f99,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k6_subset_1(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(rectify,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0)) | ~spl5_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1)) | spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f191])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    spl5_11 <=> r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ~spl5_6 | ~spl5_4 | ~spl5_11 | spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f185,f101,f191,f97,f116])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(sK1)) | ~r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0)) | ~v1_relat_1(sK1) | spl5_5),
% 0.21/0.53    inference(resolution,[],[f102,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) | spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    $false | spl5_6),
% 0.21/0.53    inference(resolution,[],[f118,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) & v1_relat_1(sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))) & v1_relat_1(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~v1_relat_1(sK1) | spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f116])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ~spl5_4 | ~spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f80,f101,f97])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) | ~r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0))),
% 0.21/0.53    inference(resolution,[],[f54,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sQ4_eqProxy(X0,X1) | ~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.53    inference(equality_proxy_replacement,[],[f32,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~sQ4_eqProxy(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0))))),
% 0.21/0.53    inference(equality_proxy_replacement,[],[f26,f53])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl5_4 | spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f101,f97])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))) | r2_hidden(sK2(k6_subset_1(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),sK0)))),k6_subset_1(k1_relat_1(sK1),sK0))),
% 0.21/0.53    inference(resolution,[],[f54,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sQ4_eqProxy(X0,X1) | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.53    inference(equality_proxy_replacement,[],[f31,f53])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (2447)------------------------------
% 0.21/0.53  % (2447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2447)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (2447)Memory used [KB]: 6396
% 0.21/0.53  % (2447)Time elapsed: 0.071 s
% 0.21/0.53  % (2447)------------------------------
% 0.21/0.53  % (2447)------------------------------
% 0.21/0.53  % (2431)Success in time 0.172 s
%------------------------------------------------------------------------------
