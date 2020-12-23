%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 689 expanded)
%              Number of leaves         :   15 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  375 (3085 expanded)
%              Number of equality atoms :   93 ( 951 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f129,f251,f254,f259,f277,f303,f310,f343,f352,f359,f375,f385,f389,f438,f443])).

fof(f443,plain,
    ( spl7_2
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl7_2
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f320,f93])).

fof(f93,plain,
    ( sK3(sK1,sK0) != k1_funct_1(sK1,sK2(sK1,sK0))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_2
  <=> sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f320,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0))
    | ~ spl7_14 ),
    inference(resolution,[],[f317,f59])).

fof(f59,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK3(sK1,X0) = k1_funct_1(sK1,sK2(sK1,X0)) ) ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),sK1)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f20,f13])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & ! [X2] :
              ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( ! [X2] :
                    ( r2_hidden(X2,k1_relat_1(X0))
                   => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
                & k1_relat_1(X0) = k1_relat_1(X1) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f55,f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(resolution,[],[f30,f14])).

fof(f14,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f317,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f314,f16])).

fof(f16,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f314,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK0 = sK1
    | ~ spl7_14 ),
    inference(resolution,[],[f300,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f300,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_14 ),
    inference(resolution,[],[f246,f50])).

fof(f50,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(sK2(sK0,X1),sK3(sK0,X1)),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f21,f17])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f246,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f438,plain,
    ( spl7_2
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | spl7_2
    | spl7_15 ),
    inference(subsumption_resolution,[],[f436,f16])).

fof(f436,plain,
    ( sK0 = sK1
    | spl7_2
    | spl7_15 ),
    inference(subsumption_resolution,[],[f430,f93])).

fof(f430,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0))
    | sK0 = sK1
    | spl7_15 ),
    inference(resolution,[],[f252,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK3(sK1,X0) = k1_funct_1(sK1,sK2(sK1,X0))
      | sK1 = X0 ) ),
    inference(resolution,[],[f59,f24])).

fof(f252,plain,
    ( r1_tarski(sK0,sK1)
    | spl7_15 ),
    inference(resolution,[],[f250,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0),k1_relat_1(sK0))
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f41,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK2(sK0,X1),sK3(sK0,X1)),sK0)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f20,f17])).

fof(f250,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_15
  <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f389,plain,
    ( spl7_15
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f252,f376])).

fof(f376,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f372,f16])).

fof(f372,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | ~ spl7_16 ),
    inference(resolution,[],[f340,f24])).

fof(f340,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f258,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),X0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f21,f13])).

fof(f258,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0),sK3(sK1,sK0)),sK0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl7_16
  <=> r2_hidden(k4_tarski(sK2(sK1,sK0),sK3(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f385,plain,
    ( spl7_4
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl7_4
    | spl7_13 ),
    inference(subsumption_resolution,[],[f383,f16])).

fof(f383,plain,
    ( sK0 = sK1
    | spl7_4
    | spl7_13 ),
    inference(subsumption_resolution,[],[f381,f105])).

fof(f105,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) != sK3(sK0,sK1)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_4
  <=> k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f381,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | sK0 = sK1
    | spl7_13 ),
    inference(resolution,[],[f226,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK3(sK0,X0) = k1_funct_1(sK0,sK2(sK0,X0))
      | sK0 = X0 ) ),
    inference(resolution,[],[f62,f24])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK3(sK0,X0) = k1_funct_1(sK0,sK2(sK0,X0)) ) ),
    inference(resolution,[],[f58,f41])).

fof(f58,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
      | k1_funct_1(sK0,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f56,f17])).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK0)
      | k1_funct_1(sK0,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK0) ) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f226,plain,
    ( r1_tarski(sK1,sK0)
    | spl7_13 ),
    inference(resolution,[],[f224,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),k1_relat_1(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(forward_demodulation,[],[f42,f15])).

fof(f15,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f40,f35])).

fof(f224,plain,
    ( ~ r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_13
  <=> r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f375,plain,
    ( spl7_4
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl7_4
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f373,f16])).

fof(f373,plain,
    ( sK0 = sK1
    | spl7_4
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f371,f105])).

fof(f371,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | sK0 = sK1
    | ~ spl7_16 ),
    inference(resolution,[],[f340,f71])).

fof(f359,plain,
    ( ~ spl7_4
    | spl7_10
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl7_4
    | spl7_10
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f170,f355])).

fof(f355,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f293,f106])).

fof(f106,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f293,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = k1_funct_1(sK1,sK2(sK0,sK1))
    | ~ spl7_15 ),
    inference(resolution,[],[f249,f12])).

fof(f12,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK0))
      | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f249,plain,
    ( r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f248])).

fof(f170,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) != sK3(sK0,sK1)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_10
  <=> k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f352,plain,
    ( ~ spl7_2
    | spl7_6
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl7_2
    | spl7_6
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f350,f344])).

fof(f344,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0))
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f327,f94])).

fof(f94,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f327,plain,
    ( k1_funct_1(sK1,sK2(sK1,sK0)) = k1_funct_1(sK0,sK2(sK1,sK0))
    | ~ spl7_13 ),
    inference(resolution,[],[f223,f12])).

fof(f223,plain,
    ( r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f350,plain,
    ( sK3(sK1,sK0) != k1_funct_1(sK0,sK2(sK1,sK0))
    | ~ spl7_2
    | spl7_6
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f127,f345])).

fof(f345,plain,
    ( sK3(sK1,sK0) = sK5(sK0,sK2(sK1,sK0))
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f325,f344])).

fof(f325,plain,
    ( k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0))
    | ~ spl7_13 ),
    inference(resolution,[],[f223,f63])).

fof(f63,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK0))
      | k1_funct_1(sK0,X1) = sK5(sK0,X1) ) ),
    inference(resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f127,plain,
    ( k1_funct_1(sK0,sK2(sK1,sK0)) != sK5(sK0,sK2(sK1,sK0))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_6
  <=> k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f343,plain,
    ( ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f340,f317])).

fof(f310,plain,
    ( spl7_3
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl7_3
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f308,f171])).

fof(f171,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f308,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) != sK3(sK0,sK1)
    | spl7_3
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f99,f305])).

fof(f305,plain,
    ( sK5(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f292,f171])).

fof(f292,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK1,sK2(sK0,sK1))
    | ~ spl7_15 ),
    inference(resolution,[],[f249,f61])).

fof(f61,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK0))
      | k1_funct_1(sK1,X1) = sK5(sK1,X1) ) ),
    inference(forward_demodulation,[],[f60,f15])).

fof(f60,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = sK5(sK1,X1)
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f57,f34])).

fof(f99,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) != sK5(sK1,sK2(sK0,sK1))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_3
  <=> k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f303,plain,
    ( spl7_13
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f300,f232])).

fof(f232,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl7_13 ),
    inference(subsumption_resolution,[],[f229,f16])).

fof(f229,plain,
    ( ~ r1_tarski(sK0,sK1)
    | sK0 = sK1
    | spl7_13 ),
    inference(resolution,[],[f226,f24])).

fof(f277,plain,
    ( ~ spl7_2
    | spl7_8
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl7_2
    | spl7_8
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f275,f141])).

fof(f141,plain,
    ( sK3(sK1,sK0) != k1_funct_1(sK0,sK2(sK1,sK0))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_8
  <=> sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f275,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0))
    | ~ spl7_2
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f271,f94])).

fof(f271,plain,
    ( k1_funct_1(sK1,sK2(sK1,sK0)) = k1_funct_1(sK0,sK2(sK1,sK0))
    | ~ spl7_13 ),
    inference(resolution,[],[f223,f12])).

fof(f259,plain,
    ( ~ spl7_13
    | spl7_16
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f240,f140,f126,f256,f222])).

fof(f240,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0),sK3(sK1,sK0)),sK0)
    | ~ r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0))
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(superposition,[],[f34,f205])).

fof(f205,plain,
    ( sK3(sK1,sK0) = sK5(sK0,sK2(sK1,sK0))
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f128,f142])).

fof(f142,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f128,plain,
    ( k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f254,plain,
    ( spl7_13
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl7_13
    | spl7_15 ),
    inference(subsumption_resolution,[],[f252,f232])).

fof(f251,plain,
    ( spl7_14
    | ~ spl7_15
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f242,f169,f98,f248,f244])).

fof(f242,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))
    | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f241,f15])).

fof(f241,plain,
    ( r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)
    | ~ r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1))
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(superposition,[],[f34,f212])).

fof(f212,plain,
    ( sK5(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f100,f171])).

fof(f100,plain,
    ( k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK1,sK2(sK0,sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f129,plain,
    ( spl7_6
    | spl7_4 ),
    inference(avatar_split_clause,[],[f124,f104,f126])).

fof(f124,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f115,f16])).

fof(f115,plain,
    ( k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)
    | sK0 = sK1
    | k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0)) ),
    inference(resolution,[],[f71,f68])).

fof(f68,plain,(
    ! [X1] :
      ( r1_tarski(sK1,X1)
      | k1_funct_1(sK0,sK2(sK1,X1)) = sK5(sK0,sK2(sK1,X1)) ) ),
    inference(resolution,[],[f63,f43])).

fof(f107,plain,
    ( spl7_4
    | spl7_2 ),
    inference(avatar_split_clause,[],[f102,f92,f104])).

fof(f102,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0))
    | k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) ),
    inference(subsumption_resolution,[],[f83,f16])).

fof(f83,plain,
    ( sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0))
    | sK0 = sK1
    | k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) ),
    inference(resolution,[],[f70,f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (30625)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.46  % (30617)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (30609)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (30625)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f444,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f107,f129,f251,f254,f259,f277,f303,f310,f343,f352,f359,f375,f385,f389,f438,f443])).
% 0.21/0.48  fof(f443,plain,(
% 0.21/0.48    spl7_2 | ~spl7_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f442])).
% 0.21/0.48  fof(f442,plain,(
% 0.21/0.48    $false | (spl7_2 | ~spl7_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f320,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    sK3(sK1,sK0) != k1_funct_1(sK1,sK2(sK1,sK0)) | spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl7_2 <=> sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0)) | ~spl7_14),
% 0.21/0.48    inference(resolution,[],[f317,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK1,X0) | sK3(sK1,X0) = k1_funct_1(sK1,sK2(sK1,X0))) )),
% 0.21/0.48    inference(resolution,[],[f57,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),sK1) | r1_tarski(sK1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f20,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (X0 != X1 & ! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((X0 != X1 & (! [X2] : (k1_funct_1(X0,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X0))) & k1_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f13])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 0.21/0.48    inference(resolution,[],[f30,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    v1_funct_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK0) | ~spl7_14),
% 0.21/0.48    inference(subsumption_resolution,[],[f314,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    sK0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK0) | sK0 = sK1 | ~spl7_14),
% 0.21/0.48    inference(resolution,[],[f300,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl7_14),
% 0.21/0.48    inference(resolution,[],[f246,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(k4_tarski(sK2(sK0,X1),sK3(sK0,X1)),X1) | r1_tarski(sK0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f21,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | ~spl7_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f244])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl7_14 <=> r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.48  fof(f438,plain,(
% 0.21/0.48    spl7_2 | spl7_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f437])).
% 0.21/0.48  fof(f437,plain,(
% 0.21/0.48    $false | (spl7_2 | spl7_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f436,f16])).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    sK0 = sK1 | (spl7_2 | spl7_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f430,f93])).
% 0.21/0.48  fof(f430,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0)) | sK0 = sK1 | spl7_15),
% 0.21/0.48    inference(resolution,[],[f252,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK1) | sK3(sK1,X0) = k1_funct_1(sK1,sK2(sK1,X0)) | sK1 = X0) )),
% 0.21/0.48    inference(resolution,[],[f59,f24])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | spl7_15),
% 0.21/0.48    inference(resolution,[],[f250,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(sK0,X0),k1_relat_1(sK0)) | r1_tarski(sK0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f41,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X1] : (r2_hidden(k4_tarski(sK2(sK0,X1),sK3(sK0,X1)),sK0) | r1_tarski(sK0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f20,f17])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) | spl7_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    spl7_15 <=> r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    spl7_15 | ~spl7_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f388])).
% 0.21/0.48  fof(f388,plain,(
% 0.21/0.48    $false | (spl7_15 | ~spl7_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f252,f376])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | ~spl7_16),
% 0.21/0.48    inference(subsumption_resolution,[],[f372,f16])).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | sK0 = sK1 | ~spl7_16),
% 0.21/0.48    inference(resolution,[],[f340,f24])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | ~spl7_16),
% 0.21/0.48    inference(resolution,[],[f258,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),X0) | r1_tarski(sK1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f21,f13])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK2(sK1,sK0),sK3(sK1,sK0)),sK0) | ~spl7_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f256])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    spl7_16 <=> r2_hidden(k4_tarski(sK2(sK1,sK0),sK3(sK1,sK0)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.48  fof(f385,plain,(
% 0.21/0.48    spl7_4 | spl7_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    $false | (spl7_4 | spl7_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f383,f16])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    sK0 = sK1 | (spl7_4 | spl7_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f381,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK0,sK1)) != sK3(sK0,sK1) | spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl7_4 <=> k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) | sK0 = sK1 | spl7_13),
% 0.21/0.48    inference(resolution,[],[f226,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK0) | sK3(sK0,X0) = k1_funct_1(sK0,sK2(sK0,X0)) | sK0 = X0) )),
% 0.21/0.48    inference(resolution,[],[f62,f24])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK0,X0) | sK3(sK0,X0) = k1_funct_1(sK0,sK2(sK0,X0))) )),
% 0.21/0.48    inference(resolution,[],[f58,f41])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f17])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~v1_relat_1(sK0) | k1_funct_1(sK0,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK0)) )),
% 0.21/0.48    inference(resolution,[],[f30,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    r1_tarski(sK1,sK0) | spl7_13),
% 0.21/0.48    inference(resolution,[],[f224,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(sK1,X0),k1_relat_1(sK0)) | r1_tarski(sK1,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f42,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK2(sK1,X0),k1_relat_1(sK1))) )),
% 0.21/0.48    inference(resolution,[],[f40,f35])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0)) | spl7_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f222])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    spl7_13 <=> r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    spl7_4 | ~spl7_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f374])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    $false | (spl7_4 | ~spl7_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f373,f16])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    sK0 = sK1 | (spl7_4 | ~spl7_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f371,f105])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) | sK0 = sK1 | ~spl7_16),
% 0.21/0.48    inference(resolution,[],[f340,f71])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    ~spl7_4 | spl7_10 | ~spl7_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f358])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    $false | (~spl7_4 | spl7_10 | ~spl7_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f355])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1) | (~spl7_4 | ~spl7_15)),
% 0.21/0.48    inference(forward_demodulation,[],[f293,f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) | ~spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK0,sK1)) = k1_funct_1(sK1,sK2(sK0,sK1)) | ~spl7_15),
% 0.21/0.48    inference(resolution,[],[f249,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK0)) | k1_funct_1(sK0,X2) = k1_funct_1(sK1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) | ~spl7_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f248])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK0,sK1)) != sK3(sK0,sK1) | spl7_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f169])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl7_10 <=> k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    ~spl7_2 | spl7_6 | ~spl7_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f351])).
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    $false | (~spl7_2 | spl7_6 | ~spl7_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f350,f344])).
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0)) | (~spl7_2 | ~spl7_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f327,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0)) | ~spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK1,sK0)) = k1_funct_1(sK0,sK2(sK1,sK0)) | ~spl7_13),
% 0.21/0.48    inference(resolution,[],[f223,f12])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0)) | ~spl7_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f222])).
% 0.21/0.48  fof(f350,plain,(
% 0.21/0.48    sK3(sK1,sK0) != k1_funct_1(sK0,sK2(sK1,sK0)) | (~spl7_2 | spl7_6 | ~spl7_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f127,f345])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    sK3(sK1,sK0) = sK5(sK0,sK2(sK1,sK0)) | (~spl7_2 | ~spl7_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f325,f344])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0)) | ~spl7_13),
% 0.21/0.48    inference(resolution,[],[f223,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK0)) | k1_funct_1(sK0,X1) = sK5(sK0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f58,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK1,sK0)) != sK5(sK0,sK2(sK1,sK0)) | spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl7_6 <=> k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    ~spl7_14 | ~spl7_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    $false | (~spl7_14 | ~spl7_16)),
% 0.21/0.48    inference(subsumption_resolution,[],[f340,f317])).
% 0.21/0.48  fof(f310,plain,(
% 0.21/0.48    spl7_3 | ~spl7_10 | ~spl7_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f309])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    $false | (spl7_3 | ~spl7_10 | ~spl7_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f308,f171])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1) | ~spl7_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f169])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK0,sK1)) != sK3(sK0,sK1) | (spl7_3 | ~spl7_10 | ~spl7_15)),
% 0.21/0.48    inference(forward_demodulation,[],[f99,f305])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    sK5(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1) | (~spl7_10 | ~spl7_15)),
% 0.21/0.48    inference(forward_demodulation,[],[f292,f171])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK1,sK2(sK0,sK1)) | ~spl7_15),
% 0.21/0.48    inference(resolution,[],[f249,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK0)) | k1_funct_1(sK1,X1) = sK5(sK1,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f60,f15])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X1] : (k1_funct_1(sK1,X1) = sK5(sK1,X1) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.21/0.48    inference(resolution,[],[f57,f34])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK0,sK1)) != sK5(sK1,sK2(sK0,sK1)) | spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl7_3 <=> k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK1,sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    spl7_13 | ~spl7_14),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    $false | (spl7_13 | ~spl7_14)),
% 0.21/0.48    inference(subsumption_resolution,[],[f300,f232])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f229,f16])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | sK0 = sK1 | spl7_13),
% 0.21/0.48    inference(resolution,[],[f226,f24])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ~spl7_2 | spl7_8 | ~spl7_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    $false | (~spl7_2 | spl7_8 | ~spl7_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f275,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    sK3(sK1,sK0) != k1_funct_1(sK0,sK2(sK1,sK0)) | spl7_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl7_8 <=> sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0)) | (~spl7_2 | ~spl7_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f271,f94])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK1,sK0)) = k1_funct_1(sK0,sK2(sK1,sK0)) | ~spl7_13),
% 0.21/0.48    inference(resolution,[],[f223,f12])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ~spl7_13 | spl7_16 | ~spl7_6 | ~spl7_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f240,f140,f126,f256,f222])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK2(sK1,sK0),sK3(sK1,sK0)),sK0) | ~r2_hidden(sK2(sK1,sK0),k1_relat_1(sK0)) | (~spl7_6 | ~spl7_8)),
% 0.21/0.48    inference(superposition,[],[f34,f205])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    sK3(sK1,sK0) = sK5(sK0,sK2(sK1,sK0)) | (~spl7_6 | ~spl7_8)),
% 0.21/0.48    inference(forward_demodulation,[],[f128,f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK0,sK2(sK1,sK0)) | ~spl7_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f140])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0)) | ~spl7_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f126])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    spl7_13 | spl7_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f253])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    $false | (spl7_13 | spl7_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f252,f232])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    spl7_14 | ~spl7_15 | ~spl7_3 | ~spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f242,f169,f98,f248,f244])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK0)) | r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | (~spl7_3 | ~spl7_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f241,f15])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK2(sK0,sK1),sK3(sK0,sK1)),sK1) | ~r2_hidden(sK2(sK0,sK1),k1_relat_1(sK1)) | (~spl7_3 | ~spl7_10)),
% 0.21/0.48    inference(superposition,[],[f34,f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    sK5(sK1,sK2(sK0,sK1)) = sK3(sK0,sK1) | (~spl7_3 | ~spl7_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f100,f171])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    k1_funct_1(sK1,sK2(sK0,sK1)) = sK5(sK1,sK2(sK0,sK1)) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl7_6 | spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f104,f126])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) | k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f16])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1) | sK0 = sK1 | k1_funct_1(sK0,sK2(sK1,sK0)) = sK5(sK0,sK2(sK1,sK0))),
% 0.21/0.48    inference(resolution,[],[f71,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(sK1,X1) | k1_funct_1(sK0,sK2(sK1,X1)) = sK5(sK0,sK2(sK1,X1))) )),
% 0.21/0.48    inference(resolution,[],[f63,f43])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl7_4 | spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f102,f92,f104])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0)) | k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f16])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    sK3(sK1,sK0) = k1_funct_1(sK1,sK2(sK1,sK0)) | sK0 = sK1 | k1_funct_1(sK0,sK2(sK0,sK1)) = sK3(sK0,sK1)),
% 0.21/0.48    inference(resolution,[],[f70,f62])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30625)------------------------------
% 0.21/0.48  % (30625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30625)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30625)Memory used [KB]: 10746
% 0.21/0.48  % (30625)Time elapsed: 0.055 s
% 0.21/0.48  % (30625)------------------------------
% 0.21/0.48  % (30625)------------------------------
% 0.21/0.49  % (30600)Success in time 0.122 s
%------------------------------------------------------------------------------
