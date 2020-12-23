%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0771+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 112 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :  186 ( 330 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f42,f46,f55,f62,f69,f81,f87,f92,f109,f114])).

fof(f114,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f110,f107,f28,f48])).

fof(f48,plain,
    ( spl3_7
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f28,plain,
    ( spl3_2
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f107,plain,
    ( spl3_16
  <=> ! [X0] : ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f110,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(resolution,[],[f108,f29])).

fof(f29,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_tarski(X0,X1) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f108,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,X0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,
    ( ~ spl3_1
    | spl3_16
    | ~ spl3_6
    | spl3_10 ),
    inference(avatar_split_clause,[],[f70,f66,f44,f107,f23])).

fof(f23,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f66,plain,
    ( spl3_10
  <=> r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,X0)))
        | ~ v1_relat_1(sK1) )
    | ~ spl3_6
    | spl3_10 ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k3_relat_1(X2))
        | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
        | ~ v1_relat_1(X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f68,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f92,plain,
    ( spl3_8
    | ~ spl3_2
    | spl3_13 ),
    inference(avatar_split_clause,[],[f88,f84,f28,f52])).

fof(f52,plain,
    ( spl3_8
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( spl3_13
  <=> r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f88,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl3_2
    | spl3_13 ),
    inference(resolution,[],[f86,f29])).

fof(f86,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(sK1,sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f84])).

fof(f87,plain,
    ( ~ spl3_13
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f82,f79,f23,f84])).

fof(f79,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(X0,sK0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f82,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(sK1,sK0)))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f80,f25])).

fof(f25,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(X0,sK0))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f79])).

fof(f81,plain,
    ( spl3_12
    | ~ spl3_5
    | spl3_9 ),
    inference(avatar_split_clause,[],[f63,f59,f40,f79])).

fof(f40,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f59,plain,
    ( spl3_9
  <=> r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(X0,sK0)))
        | ~ v1_relat_1(X0) )
    | ~ spl3_5
    | spl3_9 ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
        | ~ v1_relat_1(X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f61,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f69,plain,
    ( ~ spl3_10
    | ~ spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f57,f48,f32,f66])).

fof(f32,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(sK1))
    | ~ spl3_3
    | spl3_7 ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r2_hidden(sK2(X0,X1),X1) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f50,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f62,plain,
    ( ~ spl3_9
    | ~ spl3_3
    | spl3_8 ),
    inference(avatar_split_clause,[],[f56,f52,f32,f59])).

fof(f56,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),sK0)
    | ~ spl3_3
    | spl3_8 ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,
    ( ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f16,f52,f48])).

fof(f16,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
      | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f28])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f23])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
