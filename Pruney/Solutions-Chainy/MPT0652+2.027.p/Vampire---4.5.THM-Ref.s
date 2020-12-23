%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:56 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 148 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  234 ( 429 expanded)
%              Number of equality atoms :   70 ( 133 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f63,f69,f94,f115,f126,f140,f146,f242,f312,f313])).

fof(f313,plain,
    ( k2_funct_1(sK0) != k4_relat_1(sK0)
    | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f312,plain,
    ( ~ spl1_6
    | ~ spl1_5
    | ~ spl1_15
    | spl1_18 ),
    inference(avatar_split_clause,[],[f311,f143,f123,f54,f60])).

fof(f60,plain,
    ( spl1_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f54,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f123,plain,
    ( spl1_15
  <=> k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f143,plain,
    ( spl1_18
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f311,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_15
    | spl1_18 ),
    inference(trivial_inequality_removal,[],[f310])).

fof(f310,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_15
    | spl1_18 ),
    inference(forward_demodulation,[],[f257,f125])).

fof(f125,plain,
    ( k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f257,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_18 ),
    inference(superposition,[],[f145,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f145,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f242,plain,
    ( spl1_31
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_11
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f237,f112,f91,f60,f54,f239])).

fof(f239,plain,
    ( spl1_31
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).

fof(f91,plain,
    ( spl1_11
  <=> k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f112,plain,
    ( spl1_14
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f237,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_11
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f236,f114])).

fof(f114,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f236,plain,
    ( k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f184,f93])).

fof(f93,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f184,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f62,f56,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f56,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f146,plain,
    ( ~ spl1_18
    | spl1_1
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f141,f136,f35,f143])).

fof(f35,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f136,plain,
    ( spl1_17
  <=> k2_funct_1(sK0) = k4_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f141,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl1_1
    | ~ spl1_17 ),
    inference(backward_demodulation,[],[f37,f138])).

fof(f138,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f37,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f140,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_17
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f134,f44,f136,f49,f54])).

fof(f49,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f44,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f134,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f26,f46])).

fof(f46,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f126,plain,
    ( spl1_15
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f121,f91,f66,f60,f123])).

fof(f66,plain,
    ( spl1_7
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f121,plain,
    ( k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f120,f68])).

fof(f68,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f120,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f118,f93])).

fof(f118,plain,
    ( k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f62,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f115,plain,
    ( spl1_14
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f101,f54,f112])).

fof(f101,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f94,plain,
    ( spl1_11
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f82,f54,f91])).

fof(f82,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f69,plain,
    ( spl1_7
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f64,f54,f66])).

fof(f64,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f56,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f58,f54,f60])).

fof(f58,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f57,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f20])).

fof(f20,plain,
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

fof(f11,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f52,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f25,f39,f35])).

fof(f39,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f25,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.48  % (2600)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.48  % (2599)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.48  % (2592)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.48  % (2591)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.48  % (2592)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % (2590)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.49  % (2608)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f314,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f63,f69,f94,f115,f126,f140,f146,f242,f312,f313])).
% 0.19/0.49  fof(f313,plain,(
% 0.19/0.49    k2_funct_1(sK0) != k4_relat_1(sK0) | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.49  fof(f312,plain,(
% 0.19/0.49    ~spl1_6 | ~spl1_5 | ~spl1_15 | spl1_18),
% 0.19/0.49    inference(avatar_split_clause,[],[f311,f143,f123,f54,f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    spl1_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    spl1_5 <=> v1_relat_1(sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.19/0.49  fof(f123,plain,(
% 0.19/0.49    spl1_15 <=> k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.19/0.49  fof(f143,plain,(
% 0.19/0.49    spl1_18 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.19/0.49  fof(f311,plain,(
% 0.19/0.49    ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_15 | spl1_18)),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f310])).
% 0.19/0.49  fof(f310,plain,(
% 0.19/0.49    k2_relat_1(sK0) != k2_relat_1(sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | (~spl1_15 | spl1_18)),
% 0.19/0.49    inference(forward_demodulation,[],[f257,f125])).
% 0.19/0.49  fof(f125,plain,(
% 0.19/0.49    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | ~spl1_15),
% 0.19/0.49    inference(avatar_component_clause,[],[f123])).
% 0.19/0.49  fof(f257,plain,(
% 0.19/0.49    k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(sK0)) | spl1_18),
% 0.19/0.49    inference(superposition,[],[f145,f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.19/0.49  fof(f145,plain,(
% 0.19/0.49    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | spl1_18),
% 0.19/0.49    inference(avatar_component_clause,[],[f143])).
% 0.19/0.49  fof(f242,plain,(
% 0.19/0.49    spl1_31 | ~spl1_5 | ~spl1_6 | ~spl1_11 | ~spl1_14),
% 0.19/0.49    inference(avatar_split_clause,[],[f237,f112,f91,f60,f54,f239])).
% 0.19/0.49  fof(f239,plain,(
% 0.19/0.49    spl1_31 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_31])])).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    spl1_11 <=> k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.19/0.49  fof(f112,plain,(
% 0.19/0.49    spl1_14 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.19/0.49  fof(f237,plain,(
% 0.19/0.49    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_11 | ~spl1_14)),
% 0.19/0.49    inference(forward_demodulation,[],[f236,f114])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_14),
% 0.19/0.49    inference(avatar_component_clause,[],[f112])).
% 0.19/0.49  fof(f236,plain,(
% 0.19/0.49    k9_relat_1(sK0,k1_relat_1(sK0)) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_11)),
% 0.19/0.49    inference(forward_demodulation,[],[f184,f93])).
% 0.19/0.49  fof(f93,plain,(
% 0.19/0.49    k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) | ~spl1_11),
% 0.19/0.49    inference(avatar_component_clause,[],[f91])).
% 0.19/0.49  fof(f184,plain,(
% 0.19/0.49    k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0))) | (~spl1_5 | ~spl1_6)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f62,f56,f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.19/0.49  fof(f56,plain,(
% 0.19/0.49    v1_relat_1(sK0) | ~spl1_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f54])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    v1_relat_1(k4_relat_1(sK0)) | ~spl1_6),
% 0.19/0.49    inference(avatar_component_clause,[],[f60])).
% 0.19/0.49  fof(f146,plain,(
% 0.19/0.49    ~spl1_18 | spl1_1 | ~spl1_17),
% 0.19/0.49    inference(avatar_split_clause,[],[f141,f136,f35,f143])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.19/0.49  fof(f136,plain,(
% 0.19/0.49    spl1_17 <=> k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.19/0.49  fof(f141,plain,(
% 0.19/0.49    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) | (spl1_1 | ~spl1_17)),
% 0.19/0.49    inference(backward_demodulation,[],[f37,f138])).
% 0.19/0.49  fof(f138,plain,(
% 0.19/0.49    k2_funct_1(sK0) = k4_relat_1(sK0) | ~spl1_17),
% 0.19/0.49    inference(avatar_component_clause,[],[f136])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | spl1_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f35])).
% 0.19/0.49  fof(f140,plain,(
% 0.19/0.49    ~spl1_5 | ~spl1_4 | spl1_17 | ~spl1_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f134,f44,f136,f49,f54])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    spl1_4 <=> v1_funct_1(sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    spl1_3 <=> v2_funct_1(sK0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.19/0.49  fof(f134,plain,(
% 0.19/0.49    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.19/0.49    inference(resolution,[],[f26,f46])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    v2_funct_1(sK0) | ~spl1_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f44])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.19/0.49  fof(f126,plain,(
% 0.19/0.49    spl1_15 | ~spl1_6 | ~spl1_7 | ~spl1_11),
% 0.19/0.49    inference(avatar_split_clause,[],[f121,f91,f66,f60,f123])).
% 0.19/0.49  fof(f66,plain,(
% 0.19/0.49    spl1_7 <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.19/0.49  fof(f121,plain,(
% 0.19/0.49    k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | (~spl1_6 | ~spl1_7 | ~spl1_11)),
% 0.19/0.49    inference(forward_demodulation,[],[f120,f68])).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_7),
% 0.19/0.49    inference(avatar_component_clause,[],[f66])).
% 0.19/0.49  fof(f120,plain,(
% 0.19/0.49    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) | (~spl1_6 | ~spl1_11)),
% 0.19/0.49    inference(forward_demodulation,[],[f118,f93])).
% 0.19/0.49  fof(f118,plain,(
% 0.19/0.49    k1_relat_1(k4_relat_1(sK0)) = k10_relat_1(k4_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) | ~spl1_6),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f62,f32])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.19/0.49  fof(f115,plain,(
% 0.19/0.49    spl1_14 | ~spl1_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f101,f54,f112])).
% 0.19/0.49  fof(f101,plain,(
% 0.19/0.49    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_5),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f56,f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.19/0.49  fof(f94,plain,(
% 0.19/0.49    spl1_11 | ~spl1_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f82,f54,f91])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) | ~spl1_5),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f56,f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    spl1_7 | ~spl1_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f64,f54,f66])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f56,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    spl1_6 | ~spl1_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f58,f54,f60])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    v1_relat_1(k4_relat_1(sK0)) | ~spl1_5),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f56,f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    spl1_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f22,f54])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    v1_relat_1(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,negated_conjecture,(
% 0.19/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.19/0.49    inference(negated_conjecture,[],[f8])).
% 0.19/0.49  fof(f8,conjecture,(
% 0.19/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    spl1_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f23,f49])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    v1_funct_1(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    spl1_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f24,f44])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    v2_funct_1(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    ~spl1_1 | ~spl1_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f25,f39,f35])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (2592)------------------------------
% 0.19/0.49  % (2592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (2592)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (2592)Memory used [KB]: 10874
% 0.19/0.49  % (2592)Time elapsed: 0.092 s
% 0.19/0.49  % (2592)------------------------------
% 0.19/0.49  % (2592)------------------------------
% 0.19/0.49  % (2601)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.49  % (2585)Success in time 0.146 s
%------------------------------------------------------------------------------
