%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0606+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:17 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 102 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  172 ( 390 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f40,f45,f49,f53,f60,f67,f75])).

fof(f75,plain,
    ( spl3_1
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl3_1
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f69,f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,
    ( r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f66,f59])).

fof(f59,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_8
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK1,X0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f67,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f63,f47,f42,f37,f27,f65])).

fof(f27,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( spl3_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f63,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK1,X0))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f62,f39])).

fof(f39,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f62,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f61,f44])).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f61,plain,
    ( ! [X0] :
        ( r1_tarski(k7_relat_1(sK2,X0),k7_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f29])).

fof(f29,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f48,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f60,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f55,f51,f37,f32,f57])).

fof(f32,plain,
    ( spl3_3
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f55,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f54,f39])).

fof(f54,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f53,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f45,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f14,f42])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( r1_tarski(X2,X1)
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t210_relat_1)).

fof(f40,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f22])).

fof(f18,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
