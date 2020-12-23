%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 160 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  264 ( 461 expanded)
%              Number of equality atoms :   64 ( 132 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f76,f84,f92,f138,f144,f229,f386,f393,f415])).

fof(f415,plain,
    ( ~ spl1_6
    | ~ spl1_5
    | ~ spl1_20
    | ~ spl1_7
    | ~ spl1_8
    | spl1_35 ),
    inference(avatar_split_clause,[],[f414,f390,f89,f81,f226,f66,f73])).

fof(f73,plain,
    ( spl1_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f66,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f226,plain,
    ( spl1_20
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f81,plain,
    ( spl1_7
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f89,plain,
    ( spl1_8
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f390,plain,
    ( spl1_35
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f414,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_7
    | ~ spl1_8
    | spl1_35 ),
    inference(forward_demodulation,[],[f413,f83])).

fof(f83,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f413,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_8
    | spl1_35 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_8
    | spl1_35 ),
    inference(forward_demodulation,[],[f411,f91])).

fof(f91,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f411,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_35 ),
    inference(superposition,[],[f392,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f392,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_35 ),
    inference(avatar_component_clause,[],[f390])).

fof(f393,plain,
    ( ~ spl1_35
    | spl1_2
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f388,f134,f51,f390])).

fof(f51,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f134,plain,
    ( spl1_14
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f388,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_2
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f53,f136])).

fof(f136,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f53,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f386,plain,(
    spl1_20 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl1_20 ),
    inference(unit_resulting_resolution,[],[f228,f344])).

fof(f344,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(global_subsumption,[],[f45,f343])).

fof(f343,plain,(
    ! [X1] :
      ( r1_tarski(X1,X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f342,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f342,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f341])).

fof(f341,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f43,f97])).

fof(f97,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f94,f41])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f94,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f45,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f228,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_20 ),
    inference(avatar_component_clause,[],[f226])).

fof(f229,plain,
    ( ~ spl1_20
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | spl1_15 ),
    inference(avatar_split_clause,[],[f224,f141,f81,f73,f66,f226])).

fof(f141,plain,
    ( spl1_15
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f224,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | spl1_15 ),
    inference(forward_demodulation,[],[f218,f83])).

fof(f218,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6
    | spl1_15 ),
    inference(unit_resulting_resolution,[],[f68,f75,f143,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f143,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f75,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f68,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f144,plain,
    ( ~ spl1_15
    | spl1_1
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f139,f134,f47,f141])).

fof(f47,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f139,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_1
    | ~ spl1_14 ),
    inference(backward_demodulation,[],[f49,f136])).

fof(f49,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f138,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_14
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f132,f56,f134,f61,f66])).

fof(f61,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f56,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f132,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f42,f58])).

fof(f58,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f92,plain,
    ( spl1_8
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f85,f66,f89])).

fof(f85,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f84,plain,
    ( spl1_7
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f77,f66,f81])).

fof(f77,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f70,f66,f73])).

fof(f70,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f68,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f69,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f64,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f51,f47])).

fof(f32,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:30:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (15127)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (15129)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (15131)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (15148)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (15137)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (15130)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (15145)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (15128)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (15143)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (15126)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (15135)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (15128)Refutation not found, incomplete strategy% (15128)------------------------------
% 0.22/0.51  % (15128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15128)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15128)Memory used [KB]: 10618
% 0.22/0.51  % (15128)Time elapsed: 0.092 s
% 0.22/0.51  % (15128)------------------------------
% 0.22/0.51  % (15128)------------------------------
% 0.22/0.51  % (15148)Refutation not found, incomplete strategy% (15148)------------------------------
% 0.22/0.51  % (15148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15148)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15148)Memory used [KB]: 10618
% 0.22/0.51  % (15148)Time elapsed: 0.055 s
% 0.22/0.51  % (15148)------------------------------
% 0.22/0.51  % (15148)------------------------------
% 0.22/0.51  % (15135)Refutation not found, incomplete strategy% (15135)------------------------------
% 0.22/0.51  % (15135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15135)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15147)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (15135)Memory used [KB]: 10618
% 0.22/0.51  % (15135)Time elapsed: 0.097 s
% 0.22/0.51  % (15135)------------------------------
% 0.22/0.51  % (15135)------------------------------
% 0.22/0.51  % (15132)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15146)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (15125)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (15134)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (15131)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f416,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f76,f84,f92,f138,f144,f229,f386,f393,f415])).
% 0.22/0.52  fof(f415,plain,(
% 0.22/0.52    ~spl1_6 | ~spl1_5 | ~spl1_20 | ~spl1_7 | ~spl1_8 | spl1_35),
% 0.22/0.52    inference(avatar_split_clause,[],[f414,f390,f89,f81,f226,f66,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl1_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl1_5 <=> v1_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    spl1_20 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl1_7 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl1_8 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.52  fof(f390,plain,(
% 0.22/0.52    spl1_35 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.22/0.52  fof(f414,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_7 | ~spl1_8 | spl1_35)),
% 0.22/0.52    inference(forward_demodulation,[],[f413,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f413,plain,(
% 0.22/0.52    ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_8 | spl1_35)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f412])).
% 0.22/0.52  fof(f412,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k1_relat_1(sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_8 | spl1_35)),
% 0.22/0.52    inference(forward_demodulation,[],[f411,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f89])).
% 0.22/0.52  fof(f411,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | ~r1_tarski(k1_relat_1(k4_relat_1(sK0)),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_35),
% 0.22/0.52    inference(superposition,[],[f392,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.22/0.52  fof(f392,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_35),
% 0.22/0.52    inference(avatar_component_clause,[],[f390])).
% 0.22/0.52  fof(f393,plain,(
% 0.22/0.52    ~spl1_35 | spl1_2 | ~spl1_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f388,f134,f51,f390])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    spl1_14 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.52  fof(f388,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_2 | ~spl1_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f53,f136])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f134])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f51])).
% 0.22/0.52  fof(f386,plain,(
% 0.22/0.52    spl1_20),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f383])).
% 0.22/0.52  fof(f383,plain,(
% 0.22/0.52    $false | spl1_20),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f228,f344])).
% 0.22/0.52  fof(f344,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(global_subsumption,[],[f45,f343])).
% 0.22/0.52  fof(f343,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f342,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.52  fof(f342,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f341])).
% 0.22/0.52  fof(f341,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(k1_relat_1(k6_relat_1(X1)),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.52    inference(superposition,[],[f43,f97])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f94,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f45,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f226])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ~spl1_20 | ~spl1_5 | ~spl1_6 | ~spl1_7 | spl1_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f224,f141,f81,f73,f66,f226])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    spl1_15 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_7 | spl1_15)),
% 0.22/0.52    inference(forward_demodulation,[],[f218,f83])).
% 0.22/0.52  fof(f218,plain,(
% 0.22/0.52    ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | (~spl1_5 | ~spl1_6 | spl1_15)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f68,f75,f143,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f141])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(sK0)) | ~spl1_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    v1_relat_1(sK0) | ~spl1_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f66])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ~spl1_15 | spl1_1 | ~spl1_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f139,f134,f47,f141])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_1 | ~spl1_14)),
% 0.22/0.52    inference(backward_demodulation,[],[f49,f136])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f47])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~spl1_5 | ~spl1_4 | spl1_14 | ~spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f132,f56,f134,f61,f66])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    spl1_4 <=> v1_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    spl1_3 <=> v2_funct_1(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.22/0.52    inference(resolution,[],[f42,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    v2_funct_1(sK0) | ~spl1_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f56])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl1_8 | ~spl1_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f85,f66,f89])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f68,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    spl1_7 | ~spl1_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f77,f66,f81])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f68,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl1_6 | ~spl1_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f70,f66,f73])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    v1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f68,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    spl1_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f29,f66])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    v1_relat_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f11])).
% 0.22/0.52  fof(f11,conjecture,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    spl1_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f30,f61])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    v1_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    spl1_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f31,f56])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v2_funct_1(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ~spl1_1 | ~spl1_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f32,f51,f47])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (15131)------------------------------
% 0.22/0.52  % (15131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15131)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (15131)Memory used [KB]: 10874
% 0.22/0.52  % (15131)Time elapsed: 0.098 s
% 0.22/0.52  % (15131)------------------------------
% 0.22/0.52  % (15131)------------------------------
% 0.22/0.52  % (15132)Refutation not found, incomplete strategy% (15132)------------------------------
% 0.22/0.52  % (15132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15132)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15132)Memory used [KB]: 6140
% 0.22/0.52  % (15132)Time elapsed: 0.068 s
% 0.22/0.52  % (15132)------------------------------
% 0.22/0.52  % (15132)------------------------------
% 0.22/0.52  % (15124)Success in time 0.159 s
%------------------------------------------------------------------------------
