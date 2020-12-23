%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 150 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    7
%              Number of atoms          :  281 ( 544 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1004,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f67,f71,f75,f90,f138,f257,f297,f305,f855,f1003])).

fof(f1003,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_142 ),
    inference(avatar_contradiction_clause,[],[f1002])).

fof(f1002,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_142 ),
    inference(subsumption_resolution,[],[f1001,f49])).

fof(f49,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1001,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_142 ),
    inference(subsumption_resolution,[],[f1000,f34])).

fof(f34,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl4_1
  <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1000,plain,
    ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_142 ),
    inference(resolution,[],[f854,f44])).

fof(f44,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f854,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1))
        | ~ v1_relat_1(X0) )
    | ~ spl4_142 ),
    inference(avatar_component_clause,[],[f853])).

fof(f853,plain,
    ( spl4_142
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f855,plain,
    ( spl4_142
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f851,f295,f88,f52,f853])).

fof(f52,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f88,plain,
    ( spl4_13
  <=> ! [X3,X2,X4] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k7_relat_1(X2,X4),X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f295,plain,
    ( spl4_49
  <=> ! [X1] :
        ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k7_relat_1(sK2,sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f851,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f840,f54])).

fof(f54,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f840,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1))
        | ~ r1_tarski(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_13
    | ~ spl4_49 ),
    inference(resolution,[],[f296,f89])).

fof(f89,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(k7_relat_1(X2,X4),X3)
        | ~ r1_tarski(X2,X3)
        | ~ v1_relat_1(X2) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f88])).

fof(f296,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),X1)
        | ~ v1_relat_1(X1)
        | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1)) )
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f295])).

fof(f305,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_48 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6
    | spl4_48 ),
    inference(subsumption_resolution,[],[f303,f54])).

fof(f303,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_6
    | spl4_48 ),
    inference(resolution,[],[f293,f58])).

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

fof(f293,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl4_48
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f297,plain,
    ( ~ spl4_48
    | spl4_49
    | ~ spl4_8
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f286,f254,f65,f295,f291])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f254,plain,
    ( spl4_41
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f286,plain,
    ( ! [X1] :
        ( r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1))
        | ~ r1_tarski(k7_relat_1(sK2,sK0),X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k7_relat_1(sK2,sK0)) )
    | ~ spl4_8
    | ~ spl4_41 ),
    inference(superposition,[],[f66,f256])).

fof(f256,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f254])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f257,plain,
    ( spl4_41
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f246,f136,f37,f254])).

fof(f37,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f136,plain,
    ( spl4_22
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f246,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
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
        | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3) )
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
        ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f129,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3) )
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f70,f54])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f29,f69])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (13234)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (13233)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (13235)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (13232)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (13231)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (13228)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.45  % (13232)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f1004,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f59,f63,f67,f71,f75,f90,f138,f257,f297,f305,f855,f1003])).
% 0.22/0.45  fof(f1003,plain,(
% 0.22/0.45    spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_142),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f1002])).
% 0.22/0.45  fof(f1002,plain,(
% 0.22/0.45    $false | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_142)),
% 0.22/0.45    inference(subsumption_resolution,[],[f1001,f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    v1_relat_1(sK3) | ~spl4_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f47])).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    spl4_4 <=> v1_relat_1(sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.45  fof(f1001,plain,(
% 0.22/0.45    ~v1_relat_1(sK3) | (spl4_1 | ~spl4_3 | ~spl4_142)),
% 0.22/0.45    inference(subsumption_resolution,[],[f1000,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | spl4_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    spl4_1 <=> r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.45  fof(f1000,plain,(
% 0.22/0.45    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_142)),
% 0.22/0.45    inference(resolution,[],[f854,f44])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    r1_tarski(sK2,sK3) | ~spl4_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl4_3 <=> r1_tarski(sK2,sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.45  fof(f854,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1)) | ~v1_relat_1(X0)) ) | ~spl4_142),
% 0.22/0.45    inference(avatar_component_clause,[],[f853])).
% 0.22/0.45  fof(f853,plain,(
% 0.22/0.45    spl4_142 <=> ! [X0] : (~v1_relat_1(X0) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1)) | ~r1_tarski(sK2,X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).
% 0.22/0.45  fof(f855,plain,(
% 0.22/0.45    spl4_142 | ~spl4_5 | ~spl4_13 | ~spl4_49),
% 0.22/0.45    inference(avatar_split_clause,[],[f851,f295,f88,f52,f853])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl4_5 <=> v1_relat_1(sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    spl4_13 <=> ! [X3,X2,X4] : (~r1_tarski(X2,X3) | r1_tarski(k7_relat_1(X2,X4),X3) | ~v1_relat_1(X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.45  fof(f295,plain,(
% 0.22/0.45    spl4_49 <=> ! [X1] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1)) | ~v1_relat_1(X1) | ~r1_tarski(k7_relat_1(sK2,sK0),X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.22/0.45  fof(f851,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1)) | ~r1_tarski(sK2,X0)) ) | (~spl4_5 | ~spl4_13 | ~spl4_49)),
% 0.22/0.45    inference(subsumption_resolution,[],[f840,f54])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl4_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f52])).
% 0.22/0.45  fof(f840,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X0,sK1)) | ~r1_tarski(sK2,X0) | ~v1_relat_1(sK2)) ) | (~spl4_13 | ~spl4_49)),
% 0.22/0.45    inference(resolution,[],[f296,f89])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    ( ! [X4,X2,X3] : (r1_tarski(k7_relat_1(X2,X4),X3) | ~r1_tarski(X2,X3) | ~v1_relat_1(X2)) ) | ~spl4_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f88])).
% 0.22/0.45  fof(f296,plain,(
% 0.22/0.45    ( ! [X1] : (~r1_tarski(k7_relat_1(sK2,sK0),X1) | ~v1_relat_1(X1) | r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1))) ) | ~spl4_49),
% 0.22/0.45    inference(avatar_component_clause,[],[f295])).
% 0.22/0.45  fof(f305,plain,(
% 0.22/0.45    ~spl4_5 | ~spl4_6 | spl4_48),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f304])).
% 0.22/0.45  fof(f304,plain,(
% 0.22/0.45    $false | (~spl4_5 | ~spl4_6 | spl4_48)),
% 0.22/0.45    inference(subsumption_resolution,[],[f303,f54])).
% 0.22/0.45  fof(f303,plain,(
% 0.22/0.45    ~v1_relat_1(sK2) | (~spl4_6 | spl4_48)),
% 0.22/0.45    inference(resolution,[],[f293,f58])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl4_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f57])).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    spl4_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.45  fof(f293,plain,(
% 0.22/0.45    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl4_48),
% 0.22/0.45    inference(avatar_component_clause,[],[f291])).
% 0.22/0.45  fof(f291,plain,(
% 0.22/0.45    spl4_48 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.22/0.45  fof(f297,plain,(
% 0.22/0.45    ~spl4_48 | spl4_49 | ~spl4_8 | ~spl4_41),
% 0.22/0.45    inference(avatar_split_clause,[],[f286,f254,f65,f295,f291])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    spl4_8 <=> ! [X1,X0,X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.45  fof(f254,plain,(
% 0.22/0.45    spl4_41 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.45  fof(f286,plain,(
% 0.22/0.45    ( ! [X1] : (r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X1,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK2,sK0))) ) | (~spl4_8 | ~spl4_41)),
% 0.22/0.45    inference(superposition,[],[f66,f256])).
% 0.22/0.45  fof(f256,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | ~spl4_41),
% 0.22/0.45    inference(avatar_component_clause,[],[f254])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl4_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f65])).
% 0.22/0.45  fof(f257,plain,(
% 0.22/0.45    spl4_41 | ~spl4_2 | ~spl4_22),
% 0.22/0.45    inference(avatar_split_clause,[],[f246,f136,f37,f254])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    spl4_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    spl4_22 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.45  fof(f246,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl4_2 | ~spl4_22)),
% 0.22/0.45    inference(resolution,[],[f137,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f37])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3)) ) | ~spl4_22),
% 0.22/0.45    inference(avatar_component_clause,[],[f136])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    spl4_22 | ~spl4_5 | ~spl4_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f129,f69,f52,f136])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    spl4_9 <=> ! [X1,X0,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.45  fof(f129,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(sK2,X2) = k7_relat_1(k7_relat_1(sK2,X2),X3)) ) | (~spl4_5 | ~spl4_9)),
% 0.22/0.45    inference(resolution,[],[f70,f54])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) ) | ~spl4_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f69])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    spl4_13 | ~spl4_7 | ~spl4_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f78,f73,f61,f88])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl4_7 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    spl4_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k7_relat_1(X2,X4),X3) | ~v1_relat_1(X2)) ) | (~spl4_7 | ~spl4_10)),
% 0.22/0.45    inference(resolution,[],[f74,f62])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl4_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f61])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl4_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f73])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    spl4_10),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f73])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    spl4_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f69])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    spl4_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f65])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    spl4_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f61])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    spl4_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f57])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    spl4_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f21,f52])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f19,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl4_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f22,f47])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    v1_relat_1(sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f23,f42])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    r1_tarski(sK2,sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    spl4_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f24,f37])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ~spl4_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f32])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (13232)------------------------------
% 0.22/0.45  % (13232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (13232)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (13232)Memory used [KB]: 11129
% 0.22/0.45  % (13232)Time elapsed: 0.014 s
% 0.22/0.45  % (13232)------------------------------
% 0.22/0.45  % (13232)------------------------------
% 0.22/0.45  % (13226)Success in time 0.081 s
%------------------------------------------------------------------------------
