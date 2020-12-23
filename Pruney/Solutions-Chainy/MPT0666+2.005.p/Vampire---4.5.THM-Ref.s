%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 161 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :    7
%              Number of atoms          :  287 ( 506 expanded)
%              Number of equality atoms :   43 (  85 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f52,f56,f60,f64,f68,f72,f82,f88,f98,f114,f230,f247,f289,f314,f315,f787,f824])).

fof(f824,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_140 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_140 ),
    inference(subsumption_resolution,[],[f804,f36])).

fof(f36,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f804,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_140 ),
    inference(resolution,[],[f786,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f786,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_140 ),
    inference(avatar_component_clause,[],[f785])).

fof(f785,plain,
    ( spl3_140
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).

fof(f787,plain,
    ( spl3_140
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f779,f66,f49,f785])).

fof(f49,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f779,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0) )
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f67,f51])).

fof(f51,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f67,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f315,plain,
    ( ~ spl3_52
    | spl3_1
    | ~ spl3_8
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f290,f286,f62,f30,f296])).

fof(f296,plain,
    ( spl3_52
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f30,plain,
    ( spl3_1
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f286,plain,
    ( spl3_51
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f290,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_8
    | ~ spl3_51 ),
    inference(resolution,[],[f288,f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f288,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f286])).

fof(f314,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_6
    | spl3_52 ),
    inference(subsumption_resolution,[],[f312,f51])).

fof(f312,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_6
    | spl3_52 ),
    inference(resolution,[],[f298,f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f298,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f296])).

fof(f289,plain,
    ( spl3_51
    | ~ spl3_18
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f268,f245,f112,f286])).

fof(f112,plain,
    ( spl3_18
  <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f245,plain,
    ( spl3_42
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f268,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ spl3_18
    | ~ spl3_42 ),
    inference(superposition,[],[f246,f113])).

fof(f113,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f246,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),sK0)),sK1)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f245])).

fof(f247,plain,
    ( spl3_42
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f239,f228,f39,f245])).

fof(f228,plain,
    ( spl3_39
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f239,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),sK0)),sK1)
    | ~ spl3_3
    | ~ spl3_39 ),
    inference(resolution,[],[f229,f41])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0)),X1) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f228])).

fof(f230,plain,
    ( spl3_39
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f224,f96,f49,f228])).

fof(f96,plain,
    ( spl3_15
  <=> ! [X3,X5,X2,X4] :
        ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),X5)
        | ~ r1_tarski(X4,X5)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f224,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0)),X1) )
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f97,f51])).

fof(f97,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X4,X5)
        | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),X5) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f96])).

fof(f114,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f109,f86,f49,f112])).

fof(f86,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f109,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(resolution,[],[f87,f51])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f98,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f90,f80,f54,f96])).

fof(f80,plain,
    ( spl3_12
  <=> ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k1_relat_1(k7_relat_1(X3,X1)),X2)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f90,plain,
    ( ! [X4,X2,X5,X3] :
        ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),X5)
        | ~ r1_tarski(X4,X5)
        | ~ v1_relat_1(X2) )
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(resolution,[],[f81,f55])).

fof(f81,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X3)
        | r1_tarski(k1_relat_1(k7_relat_1(X3,X1)),X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f88,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f84,f62,f58,f54,f86])).

fof(f58,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f83,f55])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f82,plain,
    ( spl3_12
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f74,f70,f58,f80])).

fof(f70,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f74,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k1_relat_1(k7_relat_1(X3,X1)),X2)
        | ~ v1_relat_1(X3) )
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f71,f59])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f72,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
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

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
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

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f60,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f56,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
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

fof(f52,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
      | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
          | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
        | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f34,f30])).

fof(f23,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (22516)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (22517)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (22519)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (22520)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.43  % (22517)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f825,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f37,f42,f52,f56,f60,f64,f68,f72,f82,f88,f98,f114,f230,f247,f289,f314,f315,f787,f824])).
% 0.20/0.43  fof(f824,plain,(
% 0.20/0.43    spl3_2 | ~spl3_3 | ~spl3_140),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f823])).
% 0.20/0.43  fof(f823,plain,(
% 0.20/0.43    $false | (spl3_2 | ~spl3_3 | ~spl3_140)),
% 0.20/0.43    inference(subsumption_resolution,[],[f804,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) | spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl3_2 <=> k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f804,plain,(
% 0.20/0.43    k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,sK0) | (~spl3_3 | ~spl3_140)),
% 0.20/0.43    inference(resolution,[],[f786,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f786,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0)) ) | ~spl3_140),
% 0.20/0.43    inference(avatar_component_clause,[],[f785])).
% 0.20/0.43  fof(f785,plain,(
% 0.20/0.43    spl3_140 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_140])])).
% 0.20/0.43  fof(f787,plain,(
% 0.20/0.43    spl3_140 | ~spl3_5 | ~spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f779,f66,f49,f785])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl3_5 <=> v1_relat_1(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl3_9 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f779,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X1),X0)) ) | (~spl3_5 | ~spl3_9)),
% 0.20/0.43    inference(resolution,[],[f67,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    v1_relat_1(sK2) | ~spl3_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f49])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f66])).
% 0.20/0.43  fof(f315,plain,(
% 0.20/0.43    ~spl3_52 | spl3_1 | ~spl3_8 | ~spl3_51),
% 0.20/0.43    inference(avatar_split_clause,[],[f290,f286,f62,f30,f296])).
% 0.20/0.43  fof(f296,plain,(
% 0.20/0.43    spl3_52 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    spl3_1 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl3_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f286,plain,(
% 0.20/0.43    spl3_51 <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.43  fof(f290,plain,(
% 0.20/0.43    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | (~spl3_8 | ~spl3_51)),
% 0.20/0.43    inference(resolution,[],[f288,f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl3_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f62])).
% 0.20/0.43  fof(f288,plain,(
% 0.20/0.43    r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | ~spl3_51),
% 0.20/0.43    inference(avatar_component_clause,[],[f286])).
% 0.20/0.43  fof(f314,plain,(
% 0.20/0.43    ~spl3_5 | ~spl3_6 | spl3_52),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f313])).
% 0.20/0.43  fof(f313,plain,(
% 0.20/0.43    $false | (~spl3_5 | ~spl3_6 | spl3_52)),
% 0.20/0.43    inference(subsumption_resolution,[],[f312,f51])).
% 0.20/0.43  fof(f312,plain,(
% 0.20/0.43    ~v1_relat_1(sK2) | (~spl3_6 | spl3_52)),
% 0.20/0.43    inference(resolution,[],[f298,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl3_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.43  fof(f298,plain,(
% 0.20/0.43    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_52),
% 0.20/0.43    inference(avatar_component_clause,[],[f296])).
% 0.20/0.43  fof(f289,plain,(
% 0.20/0.43    spl3_51 | ~spl3_18 | ~spl3_42),
% 0.20/0.43    inference(avatar_split_clause,[],[f268,f245,f112,f286])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    spl3_18 <=> ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.43  fof(f245,plain,(
% 0.20/0.43    spl3_42 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),sK0)),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.43  fof(f268,plain,(
% 0.20/0.43    r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | (~spl3_18 | ~spl3_42)),
% 0.20/0.43    inference(superposition,[],[f246,f113])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) ) | ~spl3_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f112])).
% 0.20/0.43  fof(f246,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),sK0)),sK1)) ) | ~spl3_42),
% 0.20/0.43    inference(avatar_component_clause,[],[f245])).
% 0.20/0.43  fof(f247,plain,(
% 0.20/0.43    spl3_42 | ~spl3_3 | ~spl3_39),
% 0.20/0.43    inference(avatar_split_clause,[],[f239,f228,f39,f245])).
% 0.20/0.43  fof(f228,plain,(
% 0.20/0.43    spl3_39 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0)),X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.43  fof(f239,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X0),sK0)),sK1)) ) | (~spl3_3 | ~spl3_39)),
% 0.20/0.43    inference(resolution,[],[f229,f41])).
% 0.20/0.43  fof(f229,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0)),X1)) ) | ~spl3_39),
% 0.20/0.43    inference(avatar_component_clause,[],[f228])).
% 0.20/0.43  fof(f230,plain,(
% 0.20/0.43    spl3_39 | ~spl3_5 | ~spl3_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f224,f96,f49,f228])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    spl3_15 <=> ! [X3,X5,X2,X4] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),X5) | ~r1_tarski(X4,X5) | ~v1_relat_1(X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK2,X2),X0)),X1)) ) | (~spl3_5 | ~spl3_15)),
% 0.20/0.43    inference(resolution,[],[f97,f51])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    ( ! [X4,X2,X5,X3] : (~v1_relat_1(X2) | ~r1_tarski(X4,X5) | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),X5)) ) | ~spl3_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f96])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    spl3_18 | ~spl3_5 | ~spl3_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f109,f86,f49,f112])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    spl3_13 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) ) | (~spl3_5 | ~spl3_13)),
% 0.20/0.43    inference(resolution,[],[f87,f51])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1)) ) | ~spl3_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f86])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    spl3_15 | ~spl3_6 | ~spl3_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f90,f80,f54,f96])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl3_12 <=> ! [X1,X3,X2] : (~r1_tarski(X1,X2) | r1_tarski(k1_relat_1(k7_relat_1(X3,X1)),X2) | ~v1_relat_1(X3))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X4,X2,X5,X3] : (r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)),X5) | ~r1_tarski(X4,X5) | ~v1_relat_1(X2)) ) | (~spl3_6 | ~spl3_12)),
% 0.20/0.43    inference(resolution,[],[f81,f55])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X2,X3,X1] : (~v1_relat_1(X3) | r1_tarski(k1_relat_1(k7_relat_1(X3,X1)),X2) | ~r1_tarski(X1,X2)) ) | ~spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f80])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    spl3_13 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f84,f62,f58,f54,f86])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl3_7 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.20/0.43    inference(subsumption_resolution,[],[f83,f55])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(k7_relat_1(X0,X1),X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl3_7 | ~spl3_8)),
% 0.20/0.43    inference(resolution,[],[f63,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f58])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl3_12 | ~spl3_7 | ~spl3_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f74,f70,f58,f80])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    spl3_10 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X2,X3,X1] : (~r1_tarski(X1,X2) | r1_tarski(k1_relat_1(k7_relat_1(X3,X1)),X2) | ~v1_relat_1(X3)) ) | (~spl3_7 | ~spl3_10)),
% 0.20/0.43    inference(resolution,[],[f71,f59])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f70])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl3_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f70])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f66])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f62])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl3_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f58])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl3_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f54])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f49])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    v1_relat_1(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    (k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => ((k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (((k7_relat_1(k7_relat_1(X2,X1),X0) != k7_relat_1(X2,X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f39])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~spl3_1 | ~spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f34,f30])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    k7_relat_1(k7_relat_1(sK2,sK1),sK0) != k7_relat_1(sK2,sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (22517)------------------------------
% 0.20/0.43  % (22517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (22517)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (22517)Memory used [KB]: 11001
% 0.20/0.43  % (22517)Time elapsed: 0.019 s
% 0.20/0.43  % (22517)------------------------------
% 0.20/0.43  % (22517)------------------------------
% 0.20/0.44  % (22511)Success in time 0.077 s
%------------------------------------------------------------------------------
