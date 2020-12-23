%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0648+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 107 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :  181 ( 352 expanded)
%              Number of equality atoms :   49 ( 108 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f42,f46,f50,f54,f60,f66,f74,f78,f80])).

fof(f80,plain,
    ( spl1_2
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl1_2
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f26,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f76,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(backward_demodulation,[],[f59,f73])).

fof(f73,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_11
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f59,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl1_9
  <=> k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f78,plain,
    ( spl1_1
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl1_1
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f75,f22])).

fof(f22,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f75,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(backward_demodulation,[],[f65,f73])).

fof(f65,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_10
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f74,plain,
    ( spl1_11
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f69,f52,f39,f34,f29,f71])).

fof(f29,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f34,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f39,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f52,plain,
    ( spl1_8
  <=> ! [X0] :
        ( k2_funct_1(X0) = k4_relat_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f69,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f68,f41])).

fof(f41,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f68,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f67,f36])).

fof(f36,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f67,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k2_funct_1(X0) = k4_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f66,plain,
    ( spl1_10
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f61,f48,f39,f63])).

fof(f48,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f61,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f60,plain,
    ( spl1_9
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f55,f44,f39,f57])).

fof(f44,plain,
    ( spl1_6
  <=> ! [X0] :
        ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f55,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f18,f52])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f50,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f16,f48])).

fof(f16,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f46,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f12,f39])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
      | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
          | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
        | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
            & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f37,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f15,f24,f20])).

fof(f15,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
