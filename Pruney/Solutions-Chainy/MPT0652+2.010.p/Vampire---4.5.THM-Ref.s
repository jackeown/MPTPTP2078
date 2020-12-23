%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 144 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  267 ( 430 expanded)
%              Number of equality atoms :   66 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f64,f72,f82,f88,f135,f139,f150,f158,f245,f249,f255])).

fof(f255,plain,
    ( spl1_4
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_22 ),
    inference(avatar_split_clause,[],[f254,f243,f69,f52,f57])).

fof(f57,plain,
    ( spl1_4
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f52,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f69,plain,
    ( spl1_6
  <=> sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f243,plain,
    ( spl1_22
  <=> ! [X0] :
        ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f254,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_3
    | ~ spl1_6
    | ~ spl1_22 ),
    inference(forward_demodulation,[],[f250,f71])).

fof(f71,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f250,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0))
    | ~ spl1_3
    | ~ spl1_22 ),
    inference(resolution,[],[f244,f54])).

fof(f54,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) )
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f243])).

fof(f249,plain,(
    spl1_21 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl1_21 ),
    inference(unit_resulting_resolution,[],[f26,f241])).

fof(f241,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | spl1_21 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl1_21
  <=> v1_relat_1(k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f245,plain,
    ( ~ spl1_21
    | spl1_22
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f237,f132,f243,f239])).

fof(f132,plain,
    ( spl1_13
  <=> ! [X3,X4] :
        ( k1_relat_1(sK0) != k2_relat_1(X3)
        | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X4)) = k2_relat_1(k5_relat_1(X3,X4))
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f237,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k6_relat_1(k1_relat_1(sK0))) )
    | ~ spl1_13 ),
    inference(equality_resolution,[],[f235])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(sK0) != X0
        | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl1_13 ),
    inference(superposition,[],[f133,f28])).

fof(f28,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f133,plain,
    ( ! [X4,X3] :
        ( k1_relat_1(sK0) != k2_relat_1(X3)
        | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X4)) = k2_relat_1(k5_relat_1(X3,X4))
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X3) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f132])).

fof(f158,plain,(
    spl1_14 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl1_14 ),
    inference(unit_resulting_resolution,[],[f39,f149])).

fof(f149,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl1_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl1_14
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f150,plain,
    ( ~ spl1_14
    | spl1_5
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f145,f128,f85,f79,f52,f61,f147])).

fof(f61,plain,
    ( spl1_5
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f79,plain,
    ( spl1_7
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f85,plain,
    ( spl1_8
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f128,plain,
    ( spl1_12
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f145,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f144,f81])).

fof(f81,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f144,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f140,f87])).

fof(f87,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f140,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_12 ),
    inference(resolution,[],[f129,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(sK0))
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f30,f54])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f129,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f139,plain,
    ( ~ spl1_3
    | ~ spl1_2
    | spl1_12 ),
    inference(avatar_split_clause,[],[f137,f128,f47,f52])).

fof(f47,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f137,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_12 ),
    inference(resolution,[],[f130,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f130,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl1_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,
    ( ~ spl1_12
    | spl1_13
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f124,f85,f132,f128])).

fof(f124,plain,
    ( ! [X4,X3] :
        ( k1_relat_1(sK0) != k2_relat_1(X3)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X3)
        | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X4)) = k2_relat_1(k5_relat_1(X3,X4)) )
    | ~ spl1_8 ),
    inference(superposition,[],[f31,f87])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f88,plain,
    ( spl1_8
    | ~ spl1_3
    | ~ spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f83,f42,f47,f52,f85])).

fof(f42,plain,
    ( spl1_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f83,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f82,plain,
    ( spl1_7
    | ~ spl1_3
    | ~ spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f77,f42,f47,f52,f79])).

fof(f77,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f34,f44])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,
    ( spl1_6
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f65,f52,f69])).

fof(f65,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f29,f54])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f64,plain,
    ( ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f22,f61,f57])).

fof(f22,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f55,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 18:28:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (28650)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (28651)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (28648)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (28669)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (28659)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (28667)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (28656)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (28663)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (28660)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (28652)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (28658)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (28671)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (28668)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (28654)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (28660)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (28644)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f261,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f45,f50,f55,f64,f72,f82,f88,f135,f139,f150,f158,f245,f249,f255])).
% 0.22/0.55  fof(f255,plain,(
% 0.22/0.55    spl1_4 | ~spl1_3 | ~spl1_6 | ~spl1_22),
% 0.22/0.55    inference(avatar_split_clause,[],[f254,f243,f69,f52,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    spl1_4 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    spl1_3 <=> v1_relat_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    spl1_6 <=> sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    spl1_22 <=> ! [X0] : (k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.22/0.55  fof(f254,plain,(
% 0.22/0.55    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_3 | ~spl1_6 | ~spl1_22)),
% 0.22/0.55    inference(forward_demodulation,[],[f250,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) | ~spl1_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f69])).
% 0.22/0.55  fof(f250,plain,(
% 0.22/0.55    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) | (~spl1_3 | ~spl1_22)),
% 0.22/0.55    inference(resolution,[],[f244,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    v1_relat_1(sK0) | ~spl1_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f52])).
% 0.22/0.55  fof(f244,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0))) ) | ~spl1_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f243])).
% 0.22/0.55  fof(f249,plain,(
% 0.22/0.55    spl1_21),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f246])).
% 0.22/0.55  fof(f246,plain,(
% 0.22/0.55    $false | spl1_21),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f26,f241])).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    ~v1_relat_1(k6_relat_1(k1_relat_1(sK0))) | spl1_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f239])).
% 0.22/0.55  fof(f239,plain,(
% 0.22/0.55    spl1_21 <=> v1_relat_1(k6_relat_1(k1_relat_1(sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.55  fof(f245,plain,(
% 0.22/0.55    ~spl1_21 | spl1_22 | ~spl1_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f237,f132,f243,f239])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    spl1_13 <=> ! [X3,X4] : (k1_relat_1(sK0) != k2_relat_1(X3) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X4)) = k2_relat_1(k5_relat_1(X3,X4)) | ~v1_relat_1(X4) | ~v1_relat_1(X3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    ( ! [X0] : (k2_relat_1(k5_relat_1(k2_funct_1(sK0),X0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k6_relat_1(k1_relat_1(sK0)))) ) | ~spl1_13),
% 0.22/0.55    inference(equality_resolution,[],[f235])).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(sK0) != X0 | k2_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl1_13),
% 0.22/0.55    inference(superposition,[],[f133,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ( ! [X4,X3] : (k1_relat_1(sK0) != k2_relat_1(X3) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X4)) = k2_relat_1(k5_relat_1(X3,X4)) | ~v1_relat_1(X4) | ~v1_relat_1(X3)) ) | ~spl1_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f132])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    spl1_14),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    $false | spl1_14),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f39,f149])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | spl1_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f147])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    spl1_14 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ~spl1_14 | spl1_5 | ~spl1_3 | ~spl1_7 | ~spl1_8 | ~spl1_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f145,f128,f85,f79,f52,f61,f147])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    spl1_5 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    spl1_7 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    spl1_8 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    spl1_12 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | (~spl1_3 | ~spl1_7 | ~spl1_8 | ~spl1_12)),
% 0.22/0.55    inference(forward_demodulation,[],[f144,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f79])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_8 | ~spl1_12)),
% 0.22/0.55    inference(forward_demodulation,[],[f140,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f85])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) | k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_12)),
% 0.22/0.55    inference(resolution,[],[f129,f97])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(sK0)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK0))) ) | ~spl1_3),
% 0.22/0.55    inference(resolution,[],[f30,f54])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    v1_relat_1(k2_funct_1(sK0)) | ~spl1_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f128])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ~spl1_3 | ~spl1_2 | spl1_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f137,f128,f47,f52])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    spl1_2 <=> v1_funct_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl1_12),
% 0.22/0.55    inference(resolution,[],[f130,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    ~v1_relat_1(k2_funct_1(sK0)) | spl1_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f128])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ~spl1_12 | spl1_13 | ~spl1_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f124,f85,f132,f128])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    ( ! [X4,X3] : (k1_relat_1(sK0) != k2_relat_1(X3) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(X4) | ~v1_relat_1(X3) | k2_relat_1(k5_relat_1(k2_funct_1(sK0),X4)) = k2_relat_1(k5_relat_1(X3,X4))) ) | ~spl1_8),
% 0.22/0.55    inference(superposition,[],[f31,f87])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    spl1_8 | ~spl1_3 | ~spl1_2 | ~spl1_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f83,f42,f47,f52,f85])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    spl1_1 <=> v2_funct_1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_1),
% 0.22/0.55    inference(resolution,[],[f35,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    v2_funct_1(sK0) | ~spl1_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f42])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    spl1_7 | ~spl1_3 | ~spl1_2 | ~spl1_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f77,f42,f47,f52,f79])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_1),
% 0.22/0.55    inference(resolution,[],[f34,f44])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    spl1_6 | ~spl1_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f65,f52,f69])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) | ~spl1_3),
% 0.22/0.55    inference(resolution,[],[f29,f54])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ~spl1_4 | ~spl1_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f22,f61,f57])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f9])).
% 0.22/0.55  fof(f9,conjecture,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    spl1_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f23,f52])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    v1_relat_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    spl1_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f24,f47])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    v1_funct_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    spl1_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f25,f42])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    v2_funct_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (28660)------------------------------
% 0.22/0.55  % (28660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28660)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (28660)Memory used [KB]: 6396
% 0.22/0.55  % (28660)Time elapsed: 0.094 s
% 0.22/0.55  % (28660)------------------------------
% 0.22/0.55  % (28660)------------------------------
% 0.22/0.55  % (28645)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (28642)Success in time 0.175 s
%------------------------------------------------------------------------------
