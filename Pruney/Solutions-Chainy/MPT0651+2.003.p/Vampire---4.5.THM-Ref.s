%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 159 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  255 ( 440 expanded)
%              Number of equality atoms :   70 ( 122 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f60,f76,f82,f89,f96,f131,f137,f178,f182,f187,f188])).

fof(f188,plain,
    ( k2_funct_1(sK0) != k4_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f187,plain,
    ( spl1_14
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f186,f93,f86,f48,f134])).

fof(f134,plain,
    ( spl1_14
  <=> k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f48,plain,
    ( spl1_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f86,plain,
    ( spl1_9
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f93,plain,
    ( spl1_10
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f186,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_10 ),
    inference(forward_demodulation,[],[f185,f95])).

fof(f95,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f185,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f183,f88])).

fof(f88,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f183,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl1_3 ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0))) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f182,plain,(
    spl1_20 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl1_20 ),
    inference(unit_resulting_resolution,[],[f35,f177])).

fof(f177,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | spl1_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl1_20
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f178,plain,
    ( spl1_19
    | ~ spl1_20
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f169,f86,f48,f175,f171])).

fof(f171,plain,
    ( spl1_19
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f169,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(forward_demodulation,[],[f167,f88])).

fof(f167,plain,
    ( k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl1_3 ),
    inference(resolution,[],[f150,f50])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))
        | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(X0))) )
    | ~ spl1_3 ),
    inference(resolution,[],[f122,f25])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(X0))
        | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f28,f50])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f137,plain,
    ( ~ spl1_14
    | spl1_8
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f132,f128,f79,f134])).

fof(f79,plain,
    ( spl1_8
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f128,plain,
    ( spl1_13
  <=> k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f132,plain,
    ( k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | spl1_8
    | ~ spl1_13 ),
    inference(superposition,[],[f81,f130])).

fof(f130,plain,
    ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f81,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f131,plain,
    ( spl1_13
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f125,f48,f128])).

fof(f125,plain,
    ( k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f110,f50])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) = k9_relat_1(k4_relat_1(X0),k2_relat_1(sK0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f99,f25])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0)) )
    | ~ spl1_3 ),
    inference(resolution,[],[f27,f50])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f96,plain,
    ( ~ spl1_3
    | ~ spl1_2
    | spl1_10
    | ~ spl1_1
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f91,f73,f38,f93,f43,f48])).

fof(f43,plain,
    ( spl1_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f38,plain,
    ( spl1_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f73,plain,
    ( spl1_7
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f91,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_1
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f90,f75])).

fof(f75,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f90,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f89,plain,
    ( ~ spl1_3
    | ~ spl1_2
    | spl1_9
    | ~ spl1_1
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f84,f73,f38,f86,f43,f48])).

fof(f84,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_1
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f83,f75])).

fof(f83,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_1 ),
    inference(resolution,[],[f30,f40])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,
    ( ~ spl1_8
    | spl1_4
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f77,f73,f53,f79])).

fof(f53,plain,
    ( spl1_4
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f77,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))
    | spl1_4
    | ~ spl1_7 ),
    inference(backward_demodulation,[],[f55,f75])).

fof(f55,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f76,plain,
    ( spl1_7
    | ~ spl1_3
    | ~ spl1_2
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f71,f38,f43,f48,f73])).

fof(f71,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f29,f40])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f60,plain,
    ( ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f21,f57,f53])).

fof(f57,plain,
    ( spl1_5
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f21,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f51,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (17069)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.47  % (17061)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.48  % (17052)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (17052)Refutation not found, incomplete strategy% (17052)------------------------------
% 0.21/0.48  % (17052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17052)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17052)Memory used [KB]: 10490
% 0.21/0.48  % (17052)Time elapsed: 0.082 s
% 0.21/0.48  % (17052)------------------------------
% 0.21/0.48  % (17052)------------------------------
% 0.21/0.48  % (17060)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (17067)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (17054)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (17067)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f41,f46,f51,f60,f76,f82,f89,f96,f131,f137,f178,f182,f187,f188])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    k2_funct_1(sK0) != k4_relat_1(sK0) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl1_14 | ~spl1_3 | ~spl1_9 | ~spl1_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f186,f93,f86,f48,f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl1_14 <=> k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl1_3 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl1_9 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl1_10 <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | (~spl1_3 | ~spl1_9 | ~spl1_10)),
% 0.21/0.49    inference(forward_demodulation,[],[f185,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~spl1_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | (~spl1_3 | ~spl1_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f183,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    k2_relat_1(k4_relat_1(sK0)) = k9_relat_1(k4_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~spl1_3),
% 0.21/0.49    inference(resolution,[],[f62,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f48])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0))) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f26,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl1_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    $false | spl1_20),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f35,f177])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | spl1_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl1_20 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl1_19 | ~spl1_20 | ~spl1_3 | ~spl1_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f169,f86,f48,f175,f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl1_19 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (~spl1_3 | ~spl1_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f167,f88])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~spl1_3),
% 0.21/0.49    inference(resolution,[],[f150,f50])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(k4_relat_1(X0)))) ) | ~spl1_3),
% 0.21/0.49    inference(resolution,[],[f122,f25])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(sK0),k1_relat_1(X0)) | k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,X0))) ) | ~spl1_3),
% 0.21/0.49    inference(resolution,[],[f28,f50])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~spl1_14 | spl1_8 | ~spl1_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f132,f128,f79,f134])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl1_8 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl1_13 <=> k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    k1_relat_1(sK0) != k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | (spl1_8 | ~spl1_13)),
% 0.21/0.49    inference(superposition,[],[f81,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | spl1_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl1_13 | ~spl1_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f125,f48,f128])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) = k9_relat_1(k4_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_3),
% 0.21/0.49    inference(resolution,[],[f110,f50])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK0,k4_relat_1(X0))) = k9_relat_1(k4_relat_1(X0),k2_relat_1(sK0))) ) | ~spl1_3),
% 0.21/0.49    inference(resolution,[],[f99,f25])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK0,X0)) = k9_relat_1(X0,k2_relat_1(sK0))) ) | ~spl1_3),
% 0.21/0.49    inference(resolution,[],[f27,f50])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~spl1_3 | ~spl1_2 | spl1_10 | ~spl1_1 | ~spl1_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f73,f38,f93,f43,f48])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl1_2 <=> v1_funct_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl1_1 <=> v2_funct_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl1_7 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_1 | ~spl1_7)),
% 0.21/0.49    inference(forward_demodulation,[],[f90,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_1),
% 0.21/0.49    inference(resolution,[],[f31,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    v2_funct_1(sK0) | ~spl1_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f38])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~spl1_3 | ~spl1_2 | spl1_9 | ~spl1_1 | ~spl1_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f84,f73,f38,f86,f43,f48])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (~spl1_1 | ~spl1_7)),
% 0.21/0.49    inference(forward_demodulation,[],[f83,f75])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_1),
% 0.21/0.49    inference(resolution,[],[f30,f40])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl1_8 | spl1_4 | ~spl1_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f73,f53,f79])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl1_4 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k4_relat_1(sK0))) | (spl1_4 | ~spl1_7)),
% 0.21/0.49    inference(backward_demodulation,[],[f55,f75])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl1_7 | ~spl1_3 | ~spl1_2 | ~spl1_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f38,f43,f48,f73])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_1),
% 0.21/0.49    inference(resolution,[],[f29,f40])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~spl1_4 | ~spl1_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f57,f53])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl1_5 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl1_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f48])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl1_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f43])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl1_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f38])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v2_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17067)------------------------------
% 0.21/0.49  % (17067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17067)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17067)Memory used [KB]: 6268
% 0.21/0.49  % (17067)Time elapsed: 0.098 s
% 0.21/0.49  % (17067)------------------------------
% 0.21/0.49  % (17067)------------------------------
% 0.21/0.49  % (17068)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (17051)Success in time 0.142 s
%------------------------------------------------------------------------------
