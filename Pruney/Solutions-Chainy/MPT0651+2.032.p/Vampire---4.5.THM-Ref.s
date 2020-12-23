%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 146 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  238 ( 446 expanded)
%              Number of equality atoms :   62 ( 128 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f62,f75,f92,f100,f112,f120,f132,f157,f211])).

fof(f211,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | spl1_1
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f210,f96,f89,f34,f59,f53])).

fof(f53,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f59,plain,
    ( spl1_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f34,plain,
    ( spl1_1
  <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f89,plain,
    ( spl1_11
  <=> k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f96,plain,
    ( spl1_12
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f210,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1
    | ~ spl1_11
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f208,f91])).

fof(f91,plain,
    ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f208,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f186,f98])).

fof(f98,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f186,plain,
    ( k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_1 ),
    inference(superposition,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f36,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f157,plain,
    ( spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f156,f126,f59,f53,f38])).

fof(f38,plain,
    ( spl1_2
  <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f126,plain,
    ( spl1_17
  <=> k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f156,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f147,f128])).

fof(f128,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f147,plain,
    ( k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f55,f61,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f61,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f55,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f132,plain,
    ( spl1_17
    | ~ spl1_14
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f130,f116,f106,f126])).

fof(f106,plain,
    ( spl1_14
  <=> k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f116,plain,
    ( spl1_15
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f130,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_14
    | ~ spl1_15 ),
    inference(backward_demodulation,[],[f108,f118])).

fof(f118,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f108,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f120,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_15
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f114,f43,f116,f48,f53])).

fof(f48,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f43,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f114,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f26,f45])).

fof(f45,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f112,plain,
    ( spl1_14
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f110,f96,f72,f106])).

fof(f72,plain,
    ( spl1_8
  <=> k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f110,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))
    | ~ spl1_8
    | ~ spl1_12 ),
    inference(backward_demodulation,[],[f74,f98])).

fof(f74,plain,
    ( k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f100,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_12
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f94,f43,f96,f48,f53])).

fof(f94,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f25,f45])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f92,plain,
    ( spl1_11
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f81,f53,f89])).

fof(f81,plain,
    ( k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f55,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f75,plain,
    ( spl1_8
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f70,f59,f72])).

fof(f70,plain,
    ( k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f62,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f57,f53,f48,f59])).

fof(f57,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f55,f50,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f50,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f56,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
      | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).

fof(f19,plain,
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

fof(f10,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
            & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f51,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f24,f38,f34])).

fof(f24,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))
    | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (24230)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (24233)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (24234)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (24227)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (24228)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (24247)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (24244)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (24230)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (24232)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (24235)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (24227)Refutation not found, incomplete strategy% (24227)------------------------------
% 0.21/0.50  % (24227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24227)Memory used [KB]: 10490
% 0.21/0.50  % (24227)Time elapsed: 0.084 s
% 0.21/0.50  % (24227)------------------------------
% 0.21/0.50  % (24227)------------------------------
% 0.21/0.51  % (24241)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (24247)Refutation not found, incomplete strategy% (24247)------------------------------
% 0.21/0.51  % (24247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24247)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24247)Memory used [KB]: 10618
% 0.21/0.51  % (24247)Time elapsed: 0.045 s
% 0.21/0.51  % (24247)------------------------------
% 0.21/0.51  % (24247)------------------------------
% 0.21/0.51  % (24238)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (24224)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (24226)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (24239)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (24234)Refutation not found, incomplete strategy% (24234)------------------------------
% 0.21/0.51  % (24234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24234)Memory used [KB]: 10618
% 0.21/0.51  % (24234)Time elapsed: 0.094 s
% 0.21/0.51  % (24234)------------------------------
% 0.21/0.51  % (24234)------------------------------
% 0.21/0.51  % (24231)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (24231)Refutation not found, incomplete strategy% (24231)------------------------------
% 0.21/0.51  % (24231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24231)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24231)Memory used [KB]: 6140
% 0.21/0.51  % (24231)Time elapsed: 0.059 s
% 0.21/0.51  % (24231)------------------------------
% 0.21/0.51  % (24231)------------------------------
% 0.21/0.51  % (24242)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (24240)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f62,f75,f92,f100,f112,f120,f132,f157,f211])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~spl1_5 | ~spl1_6 | spl1_1 | ~spl1_11 | ~spl1_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f210,f96,f89,f34,f59,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl1_5 <=> v1_relat_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl1_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    spl1_1 <=> k1_relat_1(sK0) = k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl1_11 <=> k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl1_12 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (spl1_1 | ~spl1_11 | ~spl1_12)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k1_relat_1(sK0) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (spl1_1 | ~spl1_11 | ~spl1_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f208,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) | ~spl1_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k2_relat_1(sK0)) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | (spl1_1 | ~spl1_12)),
% 0.21/0.51    inference(forward_demodulation,[],[f186,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k10_relat_1(sK0,k1_relat_1(k2_funct_1(sK0))) | ~v1_relat_1(k2_funct_1(sK0)) | ~v1_relat_1(sK0) | spl1_1),
% 0.21/0.51    inference(superposition,[],[f36,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | spl1_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f34])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f156,f126,f59,f53,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    spl1_2 <=> k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl1_17 <=> k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | (~spl1_5 | ~spl1_6 | ~spl1_17)),
% 0.21/0.51    inference(forward_demodulation,[],[f147,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | ~spl1_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | (~spl1_5 | ~spl1_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f55,f61,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_relat_1(sK0) | ~spl1_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f53])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl1_17 | ~spl1_14 | ~spl1_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f130,f116,f106,f126])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl1_14 <=> k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl1_15 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | (~spl1_14 | ~spl1_15)),
% 0.21/0.51    inference(backward_demodulation,[],[f108,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | ~spl1_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f106])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ~spl1_5 | ~spl1_4 | spl1_15 | ~spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f114,f43,f116,f48,f53])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl1_4 <=> v1_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl1_3 <=> v2_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(resolution,[],[f26,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    v2_funct_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl1_14 | ~spl1_8 | ~spl1_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f110,f96,f72,f106])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl1_8 <=> k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    k2_relat_1(k2_funct_1(sK0)) = k9_relat_1(k2_funct_1(sK0),k2_relat_1(sK0)) | (~spl1_8 | ~spl1_12)),
% 0.21/0.51    inference(backward_demodulation,[],[f74,f98])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~spl1_5 | ~spl1_4 | spl1_12 | ~spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f94,f43,f96,f48,f53])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(resolution,[],[f25,f45])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl1_11 | ~spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f53,f89])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k10_relat_1(sK0,k2_relat_1(sK0)) | ~spl1_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f55,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl1_8 | ~spl1_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f59,f72])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    k9_relat_1(k2_funct_1(sK0),k1_relat_1(k2_funct_1(sK0))) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f61,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl1_6 | ~spl1_4 | ~spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f53,f48,f59])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f55,f50,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v1_funct_1(sK0) | ~spl1_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f48])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f53])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    (k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (((k1_relat_1(X0) != k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | k1_relat_1(X0) != k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl1_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f48])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f43])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~spl1_1 | ~spl1_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f38,f34])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    k1_relat_1(sK0) != k2_relat_1(k5_relat_1(sK0,k2_funct_1(sK0))) | k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,k2_funct_1(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24230)------------------------------
% 0.21/0.51  % (24230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24230)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (24230)Memory used [KB]: 10746
% 0.21/0.52  % (24230)Time elapsed: 0.087 s
% 0.21/0.52  % (24230)------------------------------
% 0.21/0.52  % (24230)------------------------------
% 0.21/0.52  % (24225)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (24223)Success in time 0.157 s
%------------------------------------------------------------------------------
