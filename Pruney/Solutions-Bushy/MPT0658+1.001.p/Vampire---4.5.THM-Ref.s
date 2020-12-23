%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0658+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:23 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 154 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  281 ( 504 expanded)
%              Number of equality atoms :   49 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f55,f61,f67,f73,f79,f85,f109,f162])).

fof(f162,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_13 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_13 ),
    inference(trivial_inequality_removal,[],[f160])).

fof(f160,plain,
    ( k6_relat_1(k2_relat_1(sK0)) != k6_relat_1(k2_relat_1(sK0))
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8
    | ~ spl1_9
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f159,f78])).

fof(f78,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl1_8
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f159,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK0))) != k6_relat_1(k2_relat_1(sK0))
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_13 ),
    inference(forward_demodulation,[],[f158,f108])).

fof(f108,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl1_13
  <=> k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f158,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK0))) != k5_relat_1(k2_funct_1(sK0),sK0)
    | spl1_1
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_9 ),
    inference(unit_resulting_resolution,[],[f54,f49,f60,f66,f72,f39,f84,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f84,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl1_9
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f39,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl1_1
  <=> sK0 = k2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f72,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl1_7
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f66,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl1_6
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f60,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl1_5
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f49,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl1_3
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f54,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f109,plain,
    ( spl1_13
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f104,f52,f47,f42,f106])).

fof(f42,plain,
    ( spl1_2
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f104,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f54,f49,f44,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f44,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f85,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f80,f52,f47,f42,f82])).

fof(f80,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f54,f49,f44,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f79,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f74,f52,f47,f42,f76])).

fof(f74,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f54,f49,f44,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,
    ( spl1_7
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f68,f52,f47,f42,f70])).

fof(f68,plain,
    ( v2_funct_1(k2_funct_1(sK0))
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f54,f49,f44,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f67,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f62,f52,f47,f64])).

fof(f62,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f54,f49,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f61,plain,
    ( spl1_5
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f56,f52,f47,f58])).

fof(f56,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(unit_resulting_resolution,[],[f54,f49,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != k2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( k2_funct_1(k2_funct_1(X0)) != X0
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( sK0 != k2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f50,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f25,f37])).

fof(f25,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
