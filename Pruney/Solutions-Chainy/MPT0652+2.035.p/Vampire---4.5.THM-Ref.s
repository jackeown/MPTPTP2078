%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:57 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 159 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  264 ( 483 expanded)
%              Number of equality atoms :   78 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f313,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f74,f90,f105,f126,f140,f146,f223,f309])).

fof(f309,plain,
    ( spl1_1
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f308,f142,f122,f71,f64,f45])).

fof(f45,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f64,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f71,plain,
    ( spl1_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f122,plain,
    ( spl1_12
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f142,plain,
    ( spl1_15
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f308,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f307,f124])).

fof(f124,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f307,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f249,f144])).

fof(f144,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f249,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f73,f66,f42,f38,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f66,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f73,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f223,plain,
    ( spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f222,f136,f87,f71,f64,f49])).

fof(f49,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f87,plain,
    ( spl1_8
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f136,plain,
    ( spl1_14
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f222,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f221,f89])).

fof(f89,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f221,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f220,f138])).

fof(f138,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f220,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f165,f112])).

fof(f112,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f66,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f165,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f66,f73,f42,f39,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(X0) != k2_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f39,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f146,plain,
    ( spl1_15
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f145,f136,f102,f142])).

fof(f102,plain,
    ( spl1_10
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f145,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(backward_demodulation,[],[f104,f138])).

fof(f104,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f140,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_14
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f134,f54,f136,f59,f64])).

fof(f59,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f54,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f134,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f33,f56])).

fof(f56,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f126,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_12
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f120,f54,f122,f59,f64])).

fof(f120,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f32,f56])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,
    ( spl1_10
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f99,f71,f102])).

fof(f99,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f90,plain,
    ( spl1_8
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f82,f64,f87])).

fof(f82,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f66,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f74,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f68,f64,f59,f71])).

fof(f68,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f66,f61,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f61,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f67,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f62,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f30,f49,f45])).

fof(f30,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:25:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (22980)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (23000)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (22996)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (22983)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (22990)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (22981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (22992)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (22987)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (22989)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (22981)Refutation not found, incomplete strategy% (22981)------------------------------
% 0.21/0.52  % (22981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22981)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22981)Memory used [KB]: 10618
% 0.21/0.52  % (22981)Time elapsed: 0.099 s
% 0.21/0.52  % (22981)------------------------------
% 0.21/0.52  % (22981)------------------------------
% 0.21/0.52  % (22985)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.52  % (22988)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.26/0.52  % (22999)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.26/0.52  % (22993)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.26/0.52  % (22982)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.26/0.52  % (22978)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.26/0.52  % (22995)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.26/0.52  % (22984)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.26/0.53  % (22991)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.26/0.53  % (22984)Refutation found. Thanks to Tanya!
% 1.26/0.53  % SZS status Theorem for theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f313,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f74,f90,f105,f126,f140,f146,f223,f309])).
% 1.26/0.53  fof(f309,plain,(
% 1.26/0.53    spl1_1 | ~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_15),
% 1.26/0.53    inference(avatar_split_clause,[],[f308,f142,f122,f71,f64,f45])).
% 1.26/0.53  fof(f45,plain,(
% 1.26/0.53    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.26/0.53  fof(f64,plain,(
% 1.26/0.53    spl1_5 <=> v1_relat_1(sK0)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.26/0.53  fof(f71,plain,(
% 1.26/0.53    spl1_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.26/0.53  fof(f122,plain,(
% 1.26/0.53    spl1_12 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.26/0.53  fof(f142,plain,(
% 1.26/0.53    spl1_15 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 1.26/0.53  fof(f308,plain,(
% 1.26/0.53    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_15)),
% 1.26/0.53    inference(forward_demodulation,[],[f307,f124])).
% 1.26/0.53  fof(f124,plain,(
% 1.26/0.53    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_12),
% 1.26/0.53    inference(avatar_component_clause,[],[f122])).
% 1.26/0.53  fof(f307,plain,(
% 1.26/0.53    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_15)),
% 1.26/0.53    inference(forward_demodulation,[],[f249,f144])).
% 1.26/0.53  fof(f144,plain,(
% 1.26/0.53    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~spl1_15),
% 1.26/0.53    inference(avatar_component_clause,[],[f142])).
% 1.26/0.53  fof(f249,plain,(
% 1.26/0.53    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) | (~spl1_5 | ~spl1_6)),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f73,f66,f42,f38,f35])).
% 1.26/0.53  fof(f35,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f20])).
% 1.26/0.53  fof(f20,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.53    inference(flattening,[],[f19])).
% 1.26/0.53  fof(f19,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f1])).
% 1.26/0.53  fof(f1,axiom,(
% 1.26/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 1.26/0.53  fof(f38,plain,(
% 1.26/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f3])).
% 1.26/0.53  fof(f3,axiom,(
% 1.26/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.26/0.53  fof(f42,plain,(
% 1.26/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.26/0.53    inference(cnf_transformation,[],[f8])).
% 1.26/0.53  fof(f8,axiom,(
% 1.26/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.26/0.53  fof(f66,plain,(
% 1.26/0.53    v1_relat_1(sK0) | ~spl1_5),
% 1.26/0.53    inference(avatar_component_clause,[],[f64])).
% 1.26/0.53  fof(f73,plain,(
% 1.26/0.53    v1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 1.26/0.53    inference(avatar_component_clause,[],[f71])).
% 1.26/0.53  fof(f223,plain,(
% 1.26/0.53    spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_8 | ~spl1_14),
% 1.26/0.53    inference(avatar_split_clause,[],[f222,f136,f87,f71,f64,f49])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.26/0.53  fof(f87,plain,(
% 1.26/0.53    spl1_8 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.26/0.53  fof(f136,plain,(
% 1.26/0.53    spl1_14 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 1.26/0.53  fof(f222,plain,(
% 1.26/0.53    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_8 | ~spl1_14)),
% 1.26/0.53    inference(forward_demodulation,[],[f221,f89])).
% 1.26/0.53  fof(f89,plain,(
% 1.26/0.53    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_8),
% 1.26/0.53    inference(avatar_component_clause,[],[f87])).
% 1.26/0.53  fof(f221,plain,(
% 1.26/0.53    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k1_relat_1(sK0))) | (~spl1_5 | ~spl1_6 | ~spl1_14)),
% 1.26/0.53    inference(forward_demodulation,[],[f220,f138])).
% 1.26/0.53  fof(f138,plain,(
% 1.26/0.53    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_14),
% 1.26/0.53    inference(avatar_component_clause,[],[f136])).
% 1.26/0.53  fof(f220,plain,(
% 1.26/0.53    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))) | (~spl1_5 | ~spl1_6)),
% 1.26/0.53    inference(forward_demodulation,[],[f165,f112])).
% 1.26/0.53  fof(f112,plain,(
% 1.26/0.53    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) ) | ~spl1_5),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f66,f31])).
% 1.26/0.53  fof(f31,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f14])).
% 1.26/0.53  fof(f14,plain,(
% 1.26/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.26/0.53    inference(ennf_transformation,[],[f5])).
% 1.26/0.53  fof(f5,axiom,(
% 1.26/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.26/0.53  fof(f165,plain,(
% 1.26/0.53    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0)) | (~spl1_5 | ~spl1_6)),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f66,f73,f42,f39,f34])).
% 1.26/0.53  fof(f34,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_relat_1(X0) != k2_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f18])).
% 1.26/0.53  fof(f18,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.53    inference(flattening,[],[f17])).
% 1.26/0.53  fof(f17,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f2])).
% 1.26/0.53  fof(f2,axiom,(
% 1.26/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 1.26/0.53  fof(f39,plain,(
% 1.26/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f3])).
% 1.26/0.53  fof(f146,plain,(
% 1.26/0.53    spl1_15 | ~spl1_10 | ~spl1_14),
% 1.26/0.53    inference(avatar_split_clause,[],[f145,f136,f102,f142])).
% 1.26/0.53  fof(f102,plain,(
% 1.26/0.53    spl1_10 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 1.26/0.53  fof(f145,plain,(
% 1.26/0.53    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl1_10 | ~spl1_14)),
% 1.26/0.53    inference(backward_demodulation,[],[f104,f138])).
% 1.26/0.53  fof(f104,plain,(
% 1.26/0.53    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_10),
% 1.26/0.53    inference(avatar_component_clause,[],[f102])).
% 1.26/0.53  fof(f140,plain,(
% 1.26/0.53    ~spl1_5 | ~spl1_4 | spl1_14 | ~spl1_3),
% 1.26/0.53    inference(avatar_split_clause,[],[f134,f54,f136,f59,f64])).
% 1.26/0.53  fof(f59,plain,(
% 1.26/0.53    spl1_4 <=> v1_funct_1(sK0)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.26/0.53  fof(f54,plain,(
% 1.26/0.53    spl1_3 <=> v2_funct_1(sK0)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.26/0.53  fof(f134,plain,(
% 1.26/0.53    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 1.26/0.53    inference(resolution,[],[f33,f56])).
% 1.26/0.53  fof(f56,plain,(
% 1.26/0.53    v2_funct_1(sK0) | ~spl1_3),
% 1.26/0.53    inference(avatar_component_clause,[],[f54])).
% 1.26/0.53  fof(f33,plain,(
% 1.26/0.53    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f16])).
% 1.26/0.53  fof(f16,plain,(
% 1.26/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.53    inference(flattening,[],[f15])).
% 1.26/0.53  fof(f15,plain,(
% 1.26/0.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,axiom,(
% 1.26/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.26/0.53  fof(f126,plain,(
% 1.26/0.53    ~spl1_5 | ~spl1_4 | spl1_12 | ~spl1_3),
% 1.26/0.53    inference(avatar_split_clause,[],[f120,f54,f122,f59,f64])).
% 1.26/0.53  fof(f120,plain,(
% 1.26/0.53    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 1.26/0.53    inference(resolution,[],[f32,f56])).
% 1.26/0.53  fof(f32,plain,(
% 1.26/0.53    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f16])).
% 1.26/0.53  fof(f105,plain,(
% 1.26/0.53    spl1_10 | ~spl1_6),
% 1.26/0.53    inference(avatar_split_clause,[],[f99,f71,f102])).
% 1.26/0.53  fof(f99,plain,(
% 1.26/0.53    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_6),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f73,f36])).
% 1.26/0.53  fof(f36,plain,(
% 1.26/0.53    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f21])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f4])).
% 1.26/0.53  fof(f4,axiom,(
% 1.26/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.26/0.53  fof(f90,plain,(
% 1.26/0.53    spl1_8 | ~spl1_5),
% 1.26/0.53    inference(avatar_split_clause,[],[f82,f64,f87])).
% 1.26/0.53  fof(f82,plain,(
% 1.26/0.53    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_5),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f66,f37])).
% 1.26/0.53  fof(f37,plain,(
% 1.26/0.53    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f22])).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f6])).
% 1.26/0.53  fof(f6,axiom,(
% 1.26/0.53    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.26/0.53  fof(f74,plain,(
% 1.26/0.53    spl1_6 | ~spl1_4 | ~spl1_5),
% 1.26/0.53    inference(avatar_split_clause,[],[f68,f64,f59,f71])).
% 1.26/0.53  fof(f68,plain,(
% 1.26/0.53    v1_relat_1(k2_funct_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 1.26/0.53    inference(unit_resulting_resolution,[],[f66,f61,f40])).
% 1.26/0.53  fof(f40,plain,(
% 1.26/0.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f24])).
% 1.26/0.53  fof(f24,plain,(
% 1.26/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.26/0.53    inference(flattening,[],[f23])).
% 1.26/0.53  fof(f23,plain,(
% 1.26/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f7])).
% 1.26/0.53  fof(f7,axiom,(
% 1.26/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.26/0.53  fof(f61,plain,(
% 1.26/0.53    v1_funct_1(sK0) | ~spl1_4),
% 1.26/0.53    inference(avatar_component_clause,[],[f59])).
% 1.26/0.53  fof(f67,plain,(
% 1.26/0.53    spl1_5),
% 1.26/0.53    inference(avatar_split_clause,[],[f27,f64])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    v1_relat_1(sK0)),
% 1.26/0.53    inference(cnf_transformation,[],[f26])).
% 1.26/0.53  fof(f26,plain,(
% 1.26/0.53    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.26/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 1.26/0.53  fof(f25,plain,(
% 1.26/0.53    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f13,plain,(
% 1.26/0.53    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.26/0.53    inference(flattening,[],[f12])).
% 1.26/0.53  fof(f12,plain,(
% 1.26/0.53    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f11])).
% 1.26/0.53  fof(f11,negated_conjecture,(
% 1.26/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.26/0.53    inference(negated_conjecture,[],[f10])).
% 1.26/0.53  fof(f10,conjecture,(
% 1.26/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 1.26/0.53  fof(f62,plain,(
% 1.26/0.53    spl1_4),
% 1.26/0.53    inference(avatar_split_clause,[],[f28,f59])).
% 1.26/0.53  fof(f28,plain,(
% 1.26/0.53    v1_funct_1(sK0)),
% 1.26/0.53    inference(cnf_transformation,[],[f26])).
% 1.26/0.53  fof(f57,plain,(
% 1.26/0.53    spl1_3),
% 1.26/0.53    inference(avatar_split_clause,[],[f29,f54])).
% 1.26/0.53  fof(f29,plain,(
% 1.26/0.53    v2_funct_1(sK0)),
% 1.26/0.53    inference(cnf_transformation,[],[f26])).
% 1.26/0.53  fof(f52,plain,(
% 1.26/0.53    ~spl1_1 | ~spl1_2),
% 1.26/0.53    inference(avatar_split_clause,[],[f30,f49,f45])).
% 1.26/0.53  fof(f30,plain,(
% 1.26/0.53    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 1.26/0.53    inference(cnf_transformation,[],[f26])).
% 1.26/0.53  % SZS output end Proof for theBenchmark
% 1.26/0.53  % (22984)------------------------------
% 1.26/0.53  % (22984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (22984)Termination reason: Refutation
% 1.26/0.53  
% 1.26/0.53  % (22984)Memory used [KB]: 10746
% 1.26/0.53  % (22984)Time elapsed: 0.113 s
% 1.26/0.53  % (22984)------------------------------
% 1.26/0.53  % (22984)------------------------------
% 1.26/0.53  % (22977)Success in time 0.169 s
%------------------------------------------------------------------------------
