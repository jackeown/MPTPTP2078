%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 159 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  277 ( 495 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f98,f129,f174,f175,f251,f340,f395])).

fof(f395,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_15
    | spl2_24 ),
    inference(avatar_split_clause,[],[f394,f335,f165,f71,f66,f56])).

fof(f56,plain,
    ( spl2_2
  <=> v1_finset_1(k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( spl2_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f71,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f165,plain,
    ( spl2_15
  <=> k10_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f335,plain,
    ( spl2_24
  <=> v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f394,plain,
    ( ~ v1_finset_1(k10_relat_1(sK1,sK0))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_15
    | spl2_24 ),
    inference(forward_demodulation,[],[f381,f167])).

fof(f167,plain,
    ( k10_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f381,plain,
    ( ~ v1_finset_1(k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0))))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_24 ),
    inference(unit_resulting_resolution,[],[f75,f91,f337,f178])).

fof(f178,plain,
    ( ! [X1] :
        ( v1_finset_1(k9_relat_1(sK1,X1))
        | ~ v1_finset_1(k1_relat_1(k7_relat_1(sK1,X1)))
        | ~ v1_funct_1(k7_relat_1(sK1,X1))
        | ~ v1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl2_5 ),
    inference(superposition,[],[f40,f114])).

fof(f114,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f73,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f40,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

fof(f337,plain,
    ( ~ v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f335])).

fof(f91,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK1,X0))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f73,f68,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f68,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f340,plain,
    ( ~ spl2_24
    | spl2_1
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f332,f247,f51,f335])).

fof(f51,plain,
    ( spl2_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f247,plain,
    ( spl2_22
  <=> r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f332,plain,
    ( ~ v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | spl2_1
    | ~ spl2_22 ),
    inference(resolution,[],[f249,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ v1_finset_1(X0) )
    | spl2_1 ),
    inference(resolution,[],[f39,f53])).

fof(f53,plain,
    ( ~ v1_finset_1(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(f249,plain,
    ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f247])).

fof(f251,plain,
    ( ~ spl2_5
    | ~ spl2_4
    | spl2_22
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f239,f170,f61,f247,f66,f71])).

fof(f61,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f170,plain,
    ( spl2_16
  <=> r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f239,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_16 ),
    inference(resolution,[],[f172,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f172,plain,
    ( r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f175,plain,
    ( ~ spl2_5
    | spl2_15
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f157,f126,f165,f71])).

fof(f126,plain,
    ( spl2_11
  <=> r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f157,plain,
    ( k10_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ spl2_11 ),
    inference(resolution,[],[f128,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f128,plain,
    ( r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f174,plain,
    ( ~ spl2_5
    | spl2_16
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f156,f126,f170,f71])).

fof(f156,plain,
    ( r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))
    | ~ v1_relat_1(sK1)
    | ~ spl2_11 ),
    inference(resolution,[],[f128,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f129,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f124,f95,f71,f61,f126])).

fof(f95,plain,
    ( spl2_8
  <=> k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f124,plain,
    ( r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f121,f97])).

fof(f97,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f121,plain,
    ( r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f73,f63,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f63,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f98,plain,
    ( spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f92,f71,f95])).

fof(f92,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f73,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f74,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v1_finset_1(sK0)
    & v1_finset_1(k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(k10_relat_1(X1,X0))
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v1_finset_1(sK0)
      & v1_finset_1(k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

% (19479)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f14,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(k10_relat_1(X1,X0))
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v1_finset_1(k10_relat_1(X1,X0))
            & r1_tarski(X0,k2_relat_1(X1)) )
         => v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v1_finset_1(k10_relat_1(X1,X0))
          & r1_tarski(X0,k2_relat_1(X1)) )
       => v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_finset_1)).

fof(f69,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f36,f61])).

fof(f36,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f37,f56])).

fof(f37,plain,(
    v1_finset_1(k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f38,f51])).

fof(f38,plain,(
    ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (19484)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (19481)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (19483)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (19485)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (19502)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (19498)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (19494)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (19502)Refutation not found, incomplete strategy% (19502)------------------------------
% 0.22/0.51  % (19502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19482)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (19486)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (19502)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19502)Memory used [KB]: 10618
% 0.22/0.51  % (19502)Time elapsed: 0.056 s
% 0.22/0.51  % (19502)------------------------------
% 0.22/0.51  % (19502)------------------------------
% 0.22/0.51  % (19480)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (19485)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (19488)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (19499)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (19491)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (19486)Refutation not found, incomplete strategy% (19486)------------------------------
% 0.22/0.52  % (19486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19486)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19486)Memory used [KB]: 6140
% 0.22/0.52  % (19486)Time elapsed: 0.070 s
% 0.22/0.52  % (19486)------------------------------
% 0.22/0.52  % (19486)------------------------------
% 0.22/0.52  % (19487)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (19500)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (19490)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (19492)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.53  % (19493)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.53  % (19497)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f404,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f98,f129,f174,f175,f251,f340,f395])).
% 0.22/0.53  fof(f395,plain,(
% 0.22/0.53    ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_15 | spl2_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f394,f335,f165,f71,f66,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl2_2 <=> v1_finset_1(k10_relat_1(sK1,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl2_4 <=> v1_funct_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl2_5 <=> v1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    spl2_15 <=> k10_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    spl2_24 <=> v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.53  fof(f394,plain,(
% 0.22/0.53    ~v1_finset_1(k10_relat_1(sK1,sK0)) | (~spl2_4 | ~spl2_5 | ~spl2_15 | spl2_24)),
% 0.22/0.53    inference(forward_demodulation,[],[f381,f167])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    k10_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~spl2_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f165])).
% 0.22/0.53  fof(f381,plain,(
% 0.22/0.53    ~v1_finset_1(k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0)))) | (~spl2_4 | ~spl2_5 | spl2_24)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f75,f91,f337,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ( ! [X1] : (v1_finset_1(k9_relat_1(sK1,X1)) | ~v1_finset_1(k1_relat_1(k7_relat_1(sK1,X1))) | ~v1_funct_1(k7_relat_1(sK1,X1)) | ~v1_relat_1(k7_relat_1(sK1,X1))) ) | ~spl2_5),
% 0.22/0.53    inference(superposition,[],[f40,f114])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    v1_relat_1(sK1) | ~spl2_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0] : (v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : ((v1_finset_1(k2_relat_1(X0)) | ~v1_finset_1(k1_relat_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_finset_1(k1_relat_1(X0)) => v1_finset_1(k2_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).
% 0.22/0.53  fof(f337,plain,(
% 0.22/0.53    ~v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | spl2_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f335])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(k7_relat_1(sK1,X0))) ) | (~spl2_4 | ~spl2_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f68,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    v1_funct_1(sK1) | ~spl2_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f66])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.53  fof(f340,plain,(
% 0.22/0.53    ~spl2_24 | spl2_1 | ~spl2_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f332,f247,f51,f335])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl2_1 <=> v1_finset_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    spl2_22 <=> r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.53  fof(f332,plain,(
% 0.22/0.53    ~v1_finset_1(k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | (spl2_1 | ~spl2_22)),
% 0.22/0.53    inference(resolution,[],[f249,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK0,X0) | ~v1_finset_1(X0)) ) | spl2_1),
% 0.22/0.53    inference(resolution,[],[f39,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ~v1_finset_1(sK0) | spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~spl2_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f247])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    ~spl2_5 | ~spl2_4 | spl2_22 | ~spl2_3 | ~spl2_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f239,f170,f61,f247,f66,f71])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl2_3 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl2_16 <=> r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ~r1_tarski(sK0,k2_relat_1(sK1)) | r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl2_16),
% 0.22/0.53    inference(resolution,[],[f172,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,k2_relat_1(X2)) | r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) | ~spl2_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f170])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ~spl2_5 | spl2_15 | ~spl2_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f157,f126,f165,f71])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    spl2_11 <=> r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    k10_relat_1(sK1,sK0) = k1_relat_1(k7_relat_1(sK1,k10_relat_1(sK1,sK0))) | ~v1_relat_1(sK1) | ~spl2_11),
% 0.22/0.53    inference(resolution,[],[f128,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) | ~spl2_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f126])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ~spl2_5 | spl2_16 | ~spl2_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f156,f126,f170,f71])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) | ~v1_relat_1(sK1) | ~spl2_11),
% 0.22/0.53    inference(resolution,[],[f128,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl2_11 | ~spl2_3 | ~spl2_5 | ~spl2_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f124,f95,f71,f61,f126])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl2_8 <=> k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) | (~spl2_3 | ~spl2_5 | ~spl2_8)),
% 0.22/0.53    inference(forward_demodulation,[],[f121,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) | ~spl2_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    r1_tarski(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl2_3 | ~spl2_5)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f63,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_relat_1(sK1)) | ~spl2_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    spl2_8 | ~spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f92,f71,f95])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) | ~spl2_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f73,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl2_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f71])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ~v1_finset_1(sK0) & v1_finset_1(k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ? [X0,X1] : (~v1_finset_1(X0) & v1_finset_1(k10_relat_1(X1,X0)) & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v1_finset_1(sK0) & v1_finset_1(k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  % (19479)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (~v1_finset_1(X0) & v1_finset_1(k10_relat_1(X1,X0)) & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1] : ((~v1_finset_1(X0) & (v1_finset_1(k10_relat_1(X1,X0)) & r1_tarski(X0,k2_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v1_finset_1(k10_relat_1(X1,X0)) & r1_tarski(X0,k2_relat_1(X1))) => v1_finset_1(X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v1_finset_1(k10_relat_1(X1,X0)) & r1_tarski(X0,k2_relat_1(X1))) => v1_finset_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_finset_1)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl2_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f66])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl2_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f61])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f56])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v1_finset_1(k10_relat_1(sK1,sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ~spl2_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f51])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ~v1_finset_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (19485)------------------------------
% 0.22/0.53  % (19485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19485)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (19485)Memory used [KB]: 11001
% 0.22/0.53  % (19485)Time elapsed: 0.102 s
% 0.22/0.53  % (19485)------------------------------
% 0.22/0.53  % (19485)------------------------------
% 0.22/0.53  % (19478)Success in time 0.168 s
%------------------------------------------------------------------------------
