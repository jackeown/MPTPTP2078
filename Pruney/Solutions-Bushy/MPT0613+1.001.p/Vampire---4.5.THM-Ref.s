%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0613+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:18 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 105 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  176 ( 355 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f44,f48,f52,f57,f63,f68,f74,f77])).

fof(f77,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f75,f72,f32,f27])).

fof(f27,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f32,plain,
    ( spl3_3
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f75,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( ~ spl3_1
    | spl3_11
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f69,f66,f42,f72,f22])).

fof(f22,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(X1),X0)
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,
    ( spl3_10
    | spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f64,f61,f37,f66])).

fof(f37,plain,
    ( spl3_4
  <=> v4_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f61,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | v4_relat_1(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,
    ( ~ v4_relat_1(sK2,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( v4_relat_1(sK2,X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,
    ( spl3_9
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f59,f55,f50,f61])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v4_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0)
        | v4_relat_1(sK2,X1) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f51,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v4_relat_1(sK2,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f51,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f53,f46,f22,f55])).

fof(f46,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v4_relat_1(X1,X0)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | v4_relat_1(sK2,X0) )
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f47,f24])).

fof(f24,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | v4_relat_1(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f52,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f48,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f44,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ~ v4_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ v4_relat_1(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v4_relat_1(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v4_relat_1(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X2] :
        ( ~ v4_relat_1(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ v4_relat_1(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v4_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f22])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
