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
% DateTime   : Thu Dec  3 12:53:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 190 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :  446 (1032 expanded)
%              Number of equality atoms :  106 ( 300 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f66,f71,f76,f94,f108,f125,f130,f261])).

fof(f261,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f258,f107])).

fof(f107,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_12
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f258,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f257,f129])).

fof(f129,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl2_15
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f257,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f256,f124])).

fof(f124,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_14
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f256,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f252,f40])).

fof(f40,plain,
    ( k2_funct_1(sK0) != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f252,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0)))
    | k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0)))
    | k2_funct_1(sK0) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(superposition,[],[f136,f93])).

fof(f93,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_10
  <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f136,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0)
        | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f135,f50])).

fof(f50,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_3
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f135,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f134,f75])).

fof(f75,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f134,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f133,f70])).

fof(f70,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_7
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f133,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f132,f65])).

fof(f65,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f132,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f131,f60])).

fof(f60,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f131,plain,
    ( ! [X0] :
        ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0))
        | sK1 = X0
        | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_2 ),
    inference(superposition,[],[f36,f45])).

fof(f45,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_2
  <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f36,plain,(
    ! [X2,X3,X1] :
      ( k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1))
      | X1 = X3
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

fof(f130,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f111,f73,f68,f53,f127])).

fof(f53,plain,
    ( spl2_4
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f111,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f55,f70,f75,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f55,plain,
    ( v2_funct_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f125,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f112,f73,f68,f53,f122])).

fof(f112,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f55,f70,f75,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f108,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f103,f73,f68,f53,f105])).

fof(f103,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f102,f75])).

fof(f102,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f80,f70])).

fof(f80,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f55,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f94,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f89,f73,f68,f53,f91])).

fof(f89,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f88,f75])).

fof(f88,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f78,f70])).

fof(f78,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f76,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f20,f73])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1)
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1)
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
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
           => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f71,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f21,f68])).

fof(f21,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f43])).

fof(f26,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f27,f38])).

fof(f27,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:11:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (17140)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (17148)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.47  % (17140)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f262,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f61,f66,f71,f76,f94,f108,f125,f130,f261])).
% 0.22/0.47  fof(f261,plain,(
% 0.22/0.47    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10 | ~spl2_12 | ~spl2_14 | ~spl2_15),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.47  fof(f260,plain,(
% 0.22/0.47    $false | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10 | ~spl2_12 | ~spl2_14 | ~spl2_15)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f259])).
% 0.22/0.47  fof(f259,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k1_relat_1(sK0)) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10 | ~spl2_12 | ~spl2_14 | ~spl2_15)),
% 0.22/0.47    inference(forward_demodulation,[],[f258,f107])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl2_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl2_12 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.47  fof(f258,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0))) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10 | ~spl2_14 | ~spl2_15)),
% 0.22/0.47    inference(subsumption_resolution,[],[f257,f129])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    v1_relat_1(k2_funct_1(sK0)) | ~spl2_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    spl2_15 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.47  fof(f257,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10 | ~spl2_14)),
% 0.22/0.47    inference(subsumption_resolution,[],[f256,f124])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    v1_funct_1(k2_funct_1(sK0)) | ~spl2_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f122])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    spl2_14 <=> v1_funct_1(k2_funct_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.47  fof(f256,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0))) | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.47    inference(subsumption_resolution,[],[f252,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    k2_funct_1(sK0) != sK1 | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl2_1 <=> k2_funct_1(sK0) = sK1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f252,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0))) | k2_funct_1(sK0) = sK1 | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f251])).
% 0.22/0.47  fof(f251,plain,(
% 0.22/0.47    k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0)) | k6_relat_1(k1_relat_1(sK0)) != k6_relat_1(k2_relat_1(k2_funct_1(sK0))) | k2_funct_1(sK0) = sK1 | ~v1_funct_1(k2_funct_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.22/0.47    inference(superposition,[],[f136,f93])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~spl2_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f91])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    spl2_10 <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(X0,sK0) | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8)),
% 0.22/0.47    inference(forward_demodulation,[],[f135,f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl2_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl2_3 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.47  fof(f135,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_7 | ~spl2_8)),
% 0.22/0.47    inference(subsumption_resolution,[],[f134,f75])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    v1_relat_1(sK0) | ~spl2_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    spl2_8 <=> v1_relat_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f133,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    v1_funct_1(sK0) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    spl2_7 <=> v1_funct_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f132,f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    v1_relat_1(sK1) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f63])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl2_6 <=> v1_relat_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl2_2 | ~spl2_5)),
% 0.22/0.47    inference(subsumption_resolution,[],[f131,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    v1_funct_1(sK1) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl2_5 <=> v1_funct_1(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(sK0)) | sK1 = X0 | k6_relat_1(k1_relat_1(sK1)) != k5_relat_1(X0,sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_2),
% 0.22/0.47    inference(superposition,[],[f36,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) | ~spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl2_2 <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(equality_resolution,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    spl2_15 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f111,f73,f68,f53,f127])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl2_4 <=> v2_funct_1(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    v1_relat_1(k2_funct_1(sK0)) | (~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f55,f70,f75,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    v2_funct_1(sK0) | ~spl2_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f53])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    spl2_14 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f112,f73,f68,f53,f122])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    v1_funct_1(k2_funct_1(sK0)) | (~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f55,f70,f75,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl2_12 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f103,f73,f68,f53,f105])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | (~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.22/0.47    inference(subsumption_resolution,[],[f102,f75])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_4 | ~spl2_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f80,f70])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_4),
% 0.22/0.47    inference(resolution,[],[f55,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    spl2_10 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f89,f73,f68,f53,f91])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | (~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.22/0.47    inference(subsumption_resolution,[],[f88,f75])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_relat_1(sK0) | (~spl2_4 | ~spl2_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f78,f70])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_4),
% 0.22/0.47    inference(resolution,[],[f55,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f73])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    v1_relat_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f18,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ? [X1] : (k2_funct_1(sK0) != X1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl2_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f68])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    v1_funct_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl2_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f63])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    v1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl2_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f58])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    v1_funct_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl2_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f53])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    v2_funct_1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl2_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f48])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f43])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f27,f38])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    k2_funct_1(sK0) != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (17140)------------------------------
% 0.22/0.47  % (17140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17140)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (17140)Memory used [KB]: 6268
% 0.22/0.47  % (17140)Time elapsed: 0.058 s
% 0.22/0.47  % (17140)------------------------------
% 0.22/0.47  % (17140)------------------------------
% 0.22/0.47  % (17126)Success in time 0.114 s
%------------------------------------------------------------------------------
