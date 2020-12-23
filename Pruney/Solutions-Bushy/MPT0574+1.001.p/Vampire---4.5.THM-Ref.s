%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0574+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 161 expanded)
%              Number of leaves         :   13 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 ( 689 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f81,f93,f120])).

fof(f120,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl9_3 ),
    inference(resolution,[],[f105,f27])).

fof(f27,plain,(
    ~ r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f6,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f105,plain,
    ( r1_tarski(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3))
    | ~ spl9_3 ),
    inference(resolution,[],[f102,f46])).

fof(f46,plain,(
    ~ r2_hidden(sK8(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)),k10_relat_1(sK4,sK3)) ),
    inference(resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK4,sK3))
      | ~ r2_hidden(sK8(k10_relat_1(sK4,sK2),k10_relat_1(sK4,sK3)),X0) ) ),
    inference(resolution,[],[f43,f27])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK8(X0,X1),X2) ) ),
    inference(resolution,[],[f37,f39])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

% (10124)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f102,plain,
    ( ! [X12] :
        ( r2_hidden(sK8(k10_relat_1(sK4,sK2),X12),k10_relat_1(sK4,sK3))
        | r1_tarski(k10_relat_1(sK4,sK2),X12) )
    | ~ spl9_3 ),
    inference(resolution,[],[f94,f38])).

% (10118)Refutation not found, incomplete strategy% (10118)------------------------------
% (10118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10118)Termination reason: Refutation not found, incomplete strategy

% (10118)Memory used [KB]: 10618
% (10118)Time elapsed: 0.107 s
% (10118)------------------------------
% (10118)------------------------------
fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k10_relat_1(sK4,sK2))
        | r2_hidden(X0,k10_relat_1(sK4,sK3)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f92,f26])).

fof(f26,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,X1)
        | ~ r2_hidden(X0,k10_relat_1(sK4,X2))
        | r2_hidden(X0,k10_relat_1(sK4,X1)) )
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_3
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k10_relat_1(sK4,X1))
        | ~ r2_hidden(X0,k10_relat_1(sK4,X2))
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f93,plain,
    ( ~ spl9_1
    | spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f89,f76,f91,f72])).

fof(f72,plain,
    ( spl9_1
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f76,plain,
    ( spl9_2
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k10_relat_1(sK4,X1))
        | ~ r2_hidden(sK7(X2,sK4,X0),X1)
        | ~ r2_hidden(X0,k10_relat_1(sK4,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

% (10119)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k10_relat_1(sK4,X1))
        | ~ r1_tarski(X2,X1)
        | ~ r2_hidden(X0,k10_relat_1(sK4,X2))
        | ~ sP1(sK4) )
    | ~ spl9_2 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k10_relat_1(sK4,X1))
        | ~ r1_tarski(X2,X1)
        | ~ r2_hidden(X0,k10_relat_1(sK4,X2))
        | ~ r2_hidden(X0,k10_relat_1(sK4,X2))
        | ~ sP1(sK4) )
    | ~ spl9_2 ),
    inference(resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,k10_relat_1(X0,X1))
      | ~ sP1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f86,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X1,sK4,X3)
        | r2_hidden(X0,k10_relat_1(sK4,X2))
        | ~ r1_tarski(X1,X2)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(X0,k10_relat_1(sK4,X1)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f85,f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X6,X7),X1) ) )
            & ( ( r2_hidden(sK7(X0,X1,X6),X0)
                & r2_hidden(k4_tarski(X6,sK7(X0,X1,X6)),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r2_hidden(k4_tarski(X3,X5),X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r2_hidden(k4_tarski(sK5(X0,X1,X2),X5),X1) )
     => ( r2_hidden(sK6(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r2_hidden(k4_tarski(X6,X8),X1) )
     => ( r2_hidden(sK7(X0,X1,X6),X0)
        & r2_hidden(k4_tarski(X6,sK7(X0,X1,X6)),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X3,X4),X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r2_hidden(k4_tarski(X3,X5),X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X6,X7),X1) ) )
            & ( ? [X8] :
                  ( r2_hidden(X8,X0)
                  & r2_hidden(k4_tarski(X6,X8),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(k4_tarski(X3,X4),X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f85,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ r2_hidden(sK7(X5,sK4,X3),X6)
        | ~ r2_hidden(X3,k10_relat_1(sK4,X5))
        | r2_hidden(X3,k10_relat_1(sK4,X4))
        | ~ r1_tarski(X6,X4) )
    | ~ spl9_2 ),
    inference(resolution,[],[f77,f37])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK7(X2,sK4,X0),X1)
        | r2_hidden(X0,k10_relat_1(sK4,X1))
        | ~ r2_hidden(X0,k10_relat_1(sK4,X2)) )
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f81,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl9_1 ),
    inference(resolution,[],[f79,f25])).

fof(f25,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,
    ( ~ v1_relat_1(sK4)
    | spl9_1 ),
    inference(resolution,[],[f74,f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f7,f10,f9])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f74,plain,
    ( ~ sP1(sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f78,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f70,f76,f72])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k10_relat_1(sK4,X1))
      | ~ r2_hidden(X0,k10_relat_1(sK4,X2))
      | ~ r2_hidden(sK7(X2,sK4,X0),X1)
      | ~ sP1(sK4) ) ),
    inference(resolution,[],[f66,f40])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,sK4,X3)
      | r2_hidden(X1,k10_relat_1(sK4,X2))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(sK7(X0,sK4,X1),X2) ) ),
    inference(resolution,[],[f65,f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK7(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),sK4)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X0,k10_relat_1(sK4,X1)) ) ),
    inference(resolution,[],[f64,f25])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,k10_relat_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(resolution,[],[f63,f36])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X3)
      | ~ r2_hidden(k4_tarski(X2,X0),X3)
      | r2_hidden(X2,k10_relat_1(X3,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f32,f40])).

fof(f32,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X7,X0)
      | ~ r2_hidden(k4_tarski(X6,X7),X1)
      | r2_hidden(X6,X2) ) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
