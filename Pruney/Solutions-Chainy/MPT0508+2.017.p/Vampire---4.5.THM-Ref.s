%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 150 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  278 ( 539 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f501,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f67,f71,f75,f90,f138,f319,f367,f380,f488,f500])).

fof(f500,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_84 ),
    inference(avatar_contradiction_clause,[],[f499])).

fof(f499,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_84 ),
    inference(subsumption_resolution,[],[f498,f49])).

fof(f49,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f498,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_84 ),
    inference(subsumption_resolution,[],[f497,f34])).

fof(f34,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f497,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_84 ),
    inference(resolution,[],[f487,f44])).

fof(f44,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f487,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl4_84
  <=> ! [X1] :
        ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f488,plain,
    ( spl4_84
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f484,f365,f65,f52,f486])).

fof(f52,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f365,plain,
    ( spl4_63
  <=> ! [X2] :
        ( r1_tarski(k7_relat_1(sK2,sK0),X2)
        | ~ r1_tarski(k7_relat_1(sK2,sK1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f484,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_5
    | ~ spl4_8
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f483,f54])).

fof(f54,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f483,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1))
        | ~ r1_tarski(sK2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_8
    | ~ spl4_63 ),
    inference(resolution,[],[f366,f66])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f366,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK1),X2)
        | r1_tarski(k7_relat_1(sK2,sK0),X2) )
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f365])).

fof(f380,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_60 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | spl4_60 ),
    inference(subsumption_resolution,[],[f378,f54])).

fof(f378,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_6
    | spl4_60 ),
    inference(resolution,[],[f355,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f355,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl4_60 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl4_60
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f367,plain,
    ( ~ spl4_60
    | spl4_63
    | ~ spl4_13
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f349,f316,f88,f365,f353])).

fof(f88,plain,
    ( spl4_13
  <=> ! [X3,X2,X4] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k7_relat_1(X2,X4),X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f316,plain,
    ( spl4_53
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f349,plain,
    ( ! [X2] :
        ( r1_tarski(k7_relat_1(sK2,sK0),X2)
        | ~ r1_tarski(k7_relat_1(sK2,sK1),X2)
        | ~ v1_relat_1(k7_relat_1(sK2,sK1)) )
    | ~ spl4_13
    | ~ spl4_53 ),
    inference(superposition,[],[f89,f318])).

fof(f318,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f316])).

fof(f89,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(k7_relat_1(X2,X4),X3)
        | ~ r1_tarski(X2,X3)
        | ~ v1_relat_1(X2) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f319,plain,
    ( spl4_53
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f308,f136,f37,f316])).

fof(f37,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f136,plain,
    ( spl4_22
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(k7_relat_1(sK2,X3),X2) = k7_relat_1(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f308,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(resolution,[],[f137,f39])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f137,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(k7_relat_1(sK2,X3),X2) = k7_relat_1(sK2,X2) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,
    ( spl4_22
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f129,f69,f52,f136])).

fof(f69,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f129,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(k7_relat_1(sK2,X3),X2) = k7_relat_1(sK2,X2) )
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f70,f54])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f90,plain,
    ( spl4_13
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f78,f73,f61,f88])).

fof(f61,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f73,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f78,plain,
    ( ! [X4,X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k7_relat_1(X2,X4),X3)
        | ~ v1_relat_1(X2) )
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f75,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f30,f73])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f67,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f63,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f55,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f50,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f37])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f32])).

fof(f25,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (20433)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.41  % (20429)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (20431)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (20429)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f501,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f67,f71,f75,f90,f138,f319,f367,f380,f488,f500])).
% 0.20/0.42  fof(f500,plain,(
% 0.20/0.42    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_84),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f499])).
% 0.20/0.42  fof(f499,plain,(
% 0.20/0.42    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_84)),
% 0.20/0.42    inference(subsumption_resolution,[],[f498,f49])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    v1_relat_1(sK3) | ~spl4_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl4_4 <=> v1_relat_1(sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.42  fof(f498,plain,(
% 0.20/0.42    ~v1_relat_1(sK3) | (spl4_1 | ~spl4_3 | ~spl4_84)),
% 0.20/0.42    inference(subsumption_resolution,[],[f497,f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | spl4_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    spl4_1 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.42  fof(f497,plain,(
% 0.20/0.42    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_84)),
% 0.20/0.42    inference(resolution,[],[f487,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.42  fof(f487,plain,(
% 0.20/0.42    ( ! [X1] : (~r1_tarski(sK2,X1) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1)) | ~v1_relat_1(X1)) ) | ~spl4_84),
% 0.20/0.42    inference(avatar_component_clause,[],[f486])).
% 0.20/0.42  fof(f486,plain,(
% 0.20/0.42    spl4_84 <=> ! [X1] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 0.20/0.42  fof(f488,plain,(
% 0.20/0.42    spl4_84 | ~spl4_5 | ~spl4_8 | ~spl4_63),
% 0.20/0.42    inference(avatar_split_clause,[],[f484,f365,f65,f52,f486])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    spl4_5 <=> v1_relat_1(sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl4_8 <=> ! [X1,X0,X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.42  fof(f365,plain,(
% 0.20/0.42    spl4_63 <=> ! [X2] : (r1_tarski(k7_relat_1(sK2,sK0),X2) | ~r1_tarski(k7_relat_1(sK2,sK1),X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.20/0.42  fof(f484,plain,(
% 0.20/0.42    ( ! [X1] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1)) ) | (~spl4_5 | ~spl4_8 | ~spl4_63)),
% 0.20/0.42    inference(subsumption_resolution,[],[f483,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f52])).
% 0.20/0.42  fof(f483,plain,(
% 0.20/0.42    ( ! [X1] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1)) | ~r1_tarski(sK2,X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | (~spl4_8 | ~spl4_63)),
% 0.20/0.42    inference(resolution,[],[f366,f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl4_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f65])).
% 0.20/0.42  fof(f366,plain,(
% 0.20/0.42    ( ! [X2] : (~r1_tarski(k7_relat_1(sK2,sK1),X2) | r1_tarski(k7_relat_1(sK2,sK0),X2)) ) | ~spl4_63),
% 0.20/0.42    inference(avatar_component_clause,[],[f365])).
% 0.20/0.42  fof(f380,plain,(
% 0.20/0.42    ~spl4_5 | ~spl4_6 | spl4_60),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f379])).
% 0.20/0.42  fof(f379,plain,(
% 0.20/0.42    $false | (~spl4_5 | ~spl4_6 | spl4_60)),
% 0.20/0.42    inference(subsumption_resolution,[],[f378,f54])).
% 0.20/0.42  fof(f378,plain,(
% 0.20/0.42    ~v1_relat_1(sK2) | (~spl4_6 | spl4_60)),
% 0.20/0.42    inference(resolution,[],[f355,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl4_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f57])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl4_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.42  fof(f355,plain,(
% 0.20/0.42    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl4_60),
% 0.20/0.42    inference(avatar_component_clause,[],[f353])).
% 0.20/0.42  fof(f353,plain,(
% 0.20/0.42    spl4_60 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.20/0.42  fof(f367,plain,(
% 0.20/0.42    ~spl4_60 | spl4_63 | ~spl4_13 | ~spl4_53),
% 0.20/0.42    inference(avatar_split_clause,[],[f349,f316,f88,f365,f353])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    spl4_13 <=> ! [X3,X2,X4] : (~r1_tarski(X2,X3) | r1_tarski(k7_relat_1(X2,X4),X3) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.42  fof(f316,plain,(
% 0.20/0.42    spl4_53 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.20/0.42  fof(f349,plain,(
% 0.20/0.42    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,sK0),X2) | ~r1_tarski(k7_relat_1(sK2,sK1),X2) | ~v1_relat_1(k7_relat_1(sK2,sK1))) ) | (~spl4_13 | ~spl4_53)),
% 0.20/0.42    inference(superposition,[],[f89,f318])).
% 0.20/0.42  fof(f318,plain,(
% 0.20/0.42    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) | ~spl4_53),
% 0.20/0.42    inference(avatar_component_clause,[],[f316])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(X2,X4),X3) | ~r1_tarski(X2,X3) | ~v1_relat_1(X2)) ) | ~spl4_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f88])).
% 0.20/0.42  fof(f319,plain,(
% 0.20/0.42    spl4_53 | ~spl4_2 | ~spl4_22),
% 0.20/0.42    inference(avatar_split_clause,[],[f308,f136,f37,f316])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    spl4_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.42  fof(f136,plain,(
% 0.20/0.42    spl4_22 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | k7_relat_1(k7_relat_1(sK2,X3),X2) = k7_relat_1(sK2,X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.42  fof(f308,plain,(
% 0.20/0.42    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) | (~spl4_2 | ~spl4_22)),
% 0.20/0.42    inference(resolution,[],[f137,f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f37])).
% 0.20/0.42  fof(f137,plain,(
% 0.20/0.42    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(k7_relat_1(sK2,X3),X2) = k7_relat_1(sK2,X2)) ) | ~spl4_22),
% 0.20/0.42    inference(avatar_component_clause,[],[f136])).
% 0.20/0.42  fof(f138,plain,(
% 0.20/0.42    spl4_22 | ~spl4_5 | ~spl4_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f129,f69,f52,f136])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl4_9 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(k7_relat_1(sK2,X3),X2) = k7_relat_1(sK2,X2)) ) | (~spl4_5 | ~spl4_9)),
% 0.20/0.42    inference(resolution,[],[f70,f54])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) ) | ~spl4_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f69])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    spl4_13 | ~spl4_7 | ~spl4_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f78,f73,f61,f88])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl4_7 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k7_relat_1(X2,X4),X3) | ~v1_relat_1(X2)) ) | (~spl4_7 | ~spl4_10)),
% 0.20/0.42    inference(resolution,[],[f74,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl4_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl4_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f73])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    spl4_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f30,f73])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl4_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f29,f69])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(flattening,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl4_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f65])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl4_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f61])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl4_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f57])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl4_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f52])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    v1_relat_1(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f19,f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl4_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f47])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    v1_relat_1(sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl4_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f42])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    r1_tarski(sK2,sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl4_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f37])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ~spl4_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f32])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (20429)------------------------------
% 0.20/0.42  % (20429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (20429)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (20429)Memory used [KB]: 10874
% 0.20/0.42  % (20429)Time elapsed: 0.014 s
% 0.20/0.42  % (20429)------------------------------
% 0.20/0.42  % (20429)------------------------------
% 0.20/0.42  % (20432)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (20423)Success in time 0.071 s
%------------------------------------------------------------------------------
