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
% DateTime   : Thu Dec  3 12:52:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 160 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :  253 ( 484 expanded)
%              Number of equality atoms :   73 ( 138 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f70,f85,f100,f113,f127,f134,f184,f263])).

fof(f263,plain,
    ( spl1_1
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f262,f130,f110,f67,f61,f42])).

fof(f42,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f61,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f67,plain,
    ( spl1_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f110,plain,
    ( spl1_12
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f130,plain,
    ( spl1_15
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f262,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f261,f112])).

fof(f112,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f110])).

fof(f261,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f213,f132])).

fof(f132,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f213,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f69,f63,f39,f35,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f63,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f184,plain,
    ( spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f183,f124,f82,f67,f61,f46])).

fof(f46,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f82,plain,
    ( spl1_8
  <=> sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f124,plain,
    ( spl1_14
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f183,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f182,f84])).

fof(f84,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f182,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f141,f126])).

fof(f126,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f141,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f63,f69,f39,f36,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(X0) != k2_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f134,plain,
    ( spl1_15
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f133,f124,f97,f130])).

fof(f97,plain,
    ( spl1_10
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f133,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(backward_demodulation,[],[f99,f126])).

fof(f99,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f127,plain,
    ( spl1_14
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f121,f61,f56,f51,f124])).

fof(f51,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f56,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f121,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f63,f58,f53,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f53,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f58,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f113,plain,
    ( spl1_12
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f107,f61,f56,f51,f110])).

fof(f107,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f63,f58,f53,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f100,plain,
    ( spl1_10
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f94,f67,f97])).

fof(f94,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f85,plain,
    ( spl1_8
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f77,f61,f82])).

fof(f77,plain,
    ( sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f63,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f70,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f65,f61,f56,f67])).

fof(f65,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f63,f58,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f64,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).

fof(f23,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f59,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f28,f46,f42])).

fof(f28,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:04:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (28979)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.48  % (28971)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.48  % (28984)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (28989)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.49  % (28973)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (28972)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (28979)Refutation not found, incomplete strategy% (28979)------------------------------
% 0.20/0.49  % (28979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28979)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28979)Memory used [KB]: 10618
% 0.20/0.49  % (28979)Time elapsed: 0.080 s
% 0.20/0.49  % (28979)------------------------------
% 0.20/0.49  % (28979)------------------------------
% 0.20/0.49  % (28972)Refutation not found, incomplete strategy% (28972)------------------------------
% 0.20/0.49  % (28972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28972)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28972)Memory used [KB]: 10490
% 0.20/0.49  % (28972)Time elapsed: 0.079 s
% 0.20/0.49  % (28972)------------------------------
% 0.20/0.49  % (28972)------------------------------
% 0.20/0.49  % (28988)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (28983)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.49  % (28974)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (28976)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (28978)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (28977)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (28981)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (28975)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (28982)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (28986)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (28975)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f70,f85,f100,f113,f127,f134,f184,f263])).
% 0.20/0.51  fof(f263,plain,(
% 0.20/0.51    spl1_1 | ~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f262,f130,f110,f67,f61,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl1_5 <=> v1_relat_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl1_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl1_12 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    spl1_15 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f261,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f110])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f213,f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~spl1_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f130])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) | (~spl1_5 | ~spl1_6)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f69,f63,f39,f35,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    v1_relat_1(sK0) | ~spl1_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f61])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    v1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f67])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_8 | ~spl1_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f183,f124,f82,f67,f61,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl1_8 <=> sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl1_14 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_8 | ~spl1_14)),
% 0.20/0.51    inference(forward_demodulation,[],[f182,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) | ~spl1_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_14)),
% 0.20/0.51    inference(forward_demodulation,[],[f141,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f124])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0)) | (~spl1_5 | ~spl1_6)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f63,f69,f39,f36,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_relat_1(X0) != k2_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl1_15 | ~spl1_10 | ~spl1_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f133,f124,f97,f130])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    spl1_10 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl1_10 | ~spl1_14)),
% 0.20/0.51    inference(backward_demodulation,[],[f99,f126])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f97])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    spl1_14 | ~spl1_3 | ~spl1_4 | ~spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f121,f61,f56,f51,f124])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    spl1_3 <=> v2_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    spl1_4 <=> v1_funct_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f63,f58,f53,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    v2_funct_1(sK0) | ~spl1_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f51])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    v1_funct_1(sK0) | ~spl1_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f56])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl1_12 | ~spl1_3 | ~spl1_4 | ~spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f107,f61,f56,f51,f110])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f63,f58,f53,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl1_10 | ~spl1_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f94,f67,f97])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_6),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f69,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl1_8 | ~spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f77,f61,f82])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) | ~spl1_5),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f63,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl1_6 | ~spl1_4 | ~spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f65,f61,f56,f67])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    v1_relat_1(k2_funct_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f63,f58,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl1_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f61])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl1_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f56])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    v1_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl1_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f51])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    v2_funct_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ~spl1_1 | ~spl1_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f46,f42])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28975)------------------------------
% 0.20/0.51  % (28975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28975)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (28975)Memory used [KB]: 10746
% 0.20/0.51  % (28975)Time elapsed: 0.064 s
% 0.20/0.51  % (28975)------------------------------
% 0.20/0.51  % (28975)------------------------------
% 0.20/0.51  % (28968)Success in time 0.156 s
%------------------------------------------------------------------------------
