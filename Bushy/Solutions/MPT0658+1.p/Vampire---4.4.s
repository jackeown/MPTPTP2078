%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t65_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:26 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 332 expanded)
%              Number of leaves         :   31 ( 147 expanded)
%              Depth                    :    8
%              Number of atoms          :  395 ( 966 expanded)
%              Number of equality atoms :   46 (  76 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f57,f64,f71,f79,f96,f105,f120,f128,f174,f181,f222,f230,f240,f250,f260,f293,f313,f426,f433,f440,f565,f572,f609])).

fof(f609,plain,
    ( ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4
    | spl1_7
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_24
    | ~ spl1_32
    | ~ spl1_34 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_24
    | ~ spl1_32
    | ~ spl1_34 ),
    inference(subsumption_resolution,[],[f607,f467])).

fof(f467,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f49,f56,f63,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t65_funct_1.p',t61_funct_1)).

fof(f63,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl1_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f56,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f49,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_0 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_0])])).

fof(f607,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_24
    | ~ spl1_32
    | ~ spl1_34 ),
    inference(forward_demodulation,[],[f603,f292])).

fof(f292,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_32 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl1_32
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_32])])).

fof(f603,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0)))
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_24
    | ~ spl1_34 ),
    inference(unit_resulting_resolution,[],[f49,f56,f78,f95,f229,f70,f312,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t65_funct_1.p',t63_funct_1)).

fof(f312,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_34 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl1_34
  <=> k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).

fof(f70,plain,
    ( k2_funct_1(k2_funct_1(sK0)) != sK0
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl1_7
  <=> k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f229,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ spl1_24 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl1_24
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f95,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl1_10
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f78,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl1_8
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f572,plain,
    ( spl1_44
    | ~ spl1_0
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f138,f126,f48,f570])).

fof(f570,plain,
    ( spl1_44
  <=> v1_relat_1(k5_relat_1(sK0,k2_funct_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_44])])).

fof(f126,plain,
    ( spl1_16
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f138,plain,
    ( v1_relat_1(k5_relat_1(sK0,k2_funct_1(k2_funct_1(sK0))))
    | ~ spl1_0
    | ~ spl1_16 ),
    inference(unit_resulting_resolution,[],[f49,f127,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t65_funct_1.p',dt_k5_relat_1)).

fof(f127,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f565,plain,
    ( spl1_42
    | ~ spl1_0
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f133,f126,f48,f563])).

fof(f563,plain,
    ( spl1_42
  <=> v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(sK0)),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_42])])).

fof(f133,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1(k2_funct_1(sK0)),sK0))
    | ~ spl1_0
    | ~ spl1_16 ),
    inference(unit_resulting_resolution,[],[f49,f127,f43])).

fof(f440,plain,
    ( spl1_40
    | ~ spl1_0
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f113,f103,f48,f438])).

fof(f438,plain,
    ( spl1_40
  <=> v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_40])])).

fof(f103,plain,
    ( spl1_12
  <=> v1_relat_1(k5_relat_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f113,plain,
    ( v1_relat_1(k5_relat_1(sK0,k5_relat_1(sK0,sK0)))
    | ~ spl1_0
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f49,f104,f43])).

fof(f104,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f433,plain,
    ( spl1_38
    | ~ spl1_0
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f109,f103,f48,f431])).

fof(f431,plain,
    ( spl1_38
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_38])])).

fof(f109,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK0,sK0),sK0))
    | ~ spl1_0
    | ~ spl1_12 ),
    inference(unit_resulting_resolution,[],[f49,f104,f43])).

fof(f426,plain,
    ( spl1_36
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f89,f77,f424])).

fof(f424,plain,
    ( spl1_36
  <=> v1_relat_1(k5_relat_1(k2_funct_1(sK0),k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_36])])).

fof(f89,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1(sK0),k2_funct_1(sK0)))
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f78,f78,f43])).

fof(f313,plain,
    ( spl1_34
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f294,f62,f55,f48,f311])).

fof(f294,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f49,f56,f63,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
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
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t65_funct_1.p',t55_funct_1)).

fof(f293,plain,
    ( spl1_32
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f251,f62,f55,f48,f291])).

fof(f251,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f49,f56,f63,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f260,plain,
    ( spl1_30
    | ~ spl1_14
    | ~ spl1_16
    | ~ spl1_26 ),
    inference(avatar_split_clause,[],[f241,f238,f126,f118,f258])).

fof(f258,plain,
    ( spl1_30
  <=> v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f118,plain,
    ( spl1_14
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f238,plain,
    ( spl1_26
  <=> v2_funct_1(k2_funct_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f241,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK0))))
    | ~ spl1_14
    | ~ spl1_16
    | ~ spl1_26 ),
    inference(unit_resulting_resolution,[],[f127,f119,f239,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t65_funct_1.p',fc6_funct_1)).

fof(f239,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f119,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f250,plain,
    ( spl1_28
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f140,f126,f118,f248])).

fof(f248,plain,
    ( spl1_28
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f140,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK0))))
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(unit_resulting_resolution,[],[f119,f127,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t65_funct_1.p',dt_k2_funct_1)).

fof(f240,plain,
    ( spl1_26
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_24 ),
    inference(avatar_split_clause,[],[f231,f228,f94,f77,f238])).

fof(f231,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ spl1_8
    | ~ spl1_10
    | ~ spl1_24 ),
    inference(unit_resulting_resolution,[],[f78,f95,f229,f35])).

fof(f230,plain,
    ( spl1_24
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f223,f62,f55,f48,f228])).

fof(f223,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ spl1_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f49,f56,f63,f35])).

fof(f222,plain,
    ( spl1_22
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f139,f126,f118,f220])).

fof(f220,plain,
    ( spl1_22
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f139,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK0))))
    | ~ spl1_14
    | ~ spl1_16 ),
    inference(unit_resulting_resolution,[],[f119,f127,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f181,plain,
    ( spl1_20
    | ~ spl1_0
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f87,f77,f48,f179])).

fof(f179,plain,
    ( spl1_20
  <=> v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f87,plain,
    ( v1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_0
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f49,f78,f43])).

fof(f174,plain,
    ( spl1_18
    | ~ spl1_0
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f83,f77,f48,f172])).

fof(f172,plain,
    ( spl1_18
  <=> v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f83,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_0
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f78,f49,f43])).

fof(f128,plain,
    ( spl1_16
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f98,f94,f77,f126])).

fof(f98,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(unit_resulting_resolution,[],[f78,f95,f36])).

fof(f120,plain,
    ( spl1_14
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f97,f94,f77,f118])).

fof(f97,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ spl1_8
    | ~ spl1_10 ),
    inference(unit_resulting_resolution,[],[f78,f95,f37])).

fof(f105,plain,
    ( spl1_12
    | ~ spl1_0 ),
    inference(avatar_split_clause,[],[f81,f48,f103])).

fof(f81,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK0))
    | ~ spl1_0 ),
    inference(unit_resulting_resolution,[],[f49,f49,f43])).

fof(f96,plain,
    ( spl1_10
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f80,f55,f48,f94])).

fof(f80,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f49,f56,f37])).

fof(f79,plain,
    ( spl1_8
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f72,f55,f48,f77])).

fof(f72,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_0
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f49,f56,f36])).

fof(f71,plain,(
    ~ spl1_7 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    k2_funct_1(k2_funct_1(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_funct_1(k2_funct_1(sK0)) != sK0
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( k2_funct_1(k2_funct_1(sK0)) != sK0
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t65_funct_1.p',t65_funct_1)).

fof(f64,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    spl1_0 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
