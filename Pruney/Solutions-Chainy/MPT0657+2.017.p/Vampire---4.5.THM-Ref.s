%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 230 expanded)
%              Number of leaves         :   11 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  282 (1225 expanded)
%              Number of equality atoms :   92 ( 445 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f104,f119,f132])).

fof(f132,plain,(
    ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f130,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f130,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f129,f28])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f129,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,
    ( ! [X1] :
        ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_8
  <=> ! [X1] :
        ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f119,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f117,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f117,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f40,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f39,f27])).

fof(f39,plain,
    ( sK1 != k4_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f38,f23])).

fof(f23,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,
    ( sK1 != k4_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f37,f28])).

fof(f37,plain,
    ( sK1 != k4_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f26,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f116,plain,
    ( sK1 = k4_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(superposition,[],[f31,f115])).

fof(f115,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f114,f21])).

fof(f114,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f113,f92])).

fof(f92,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_6
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f113,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f111,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f111,plain,
    ( sK0 = k4_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(superposition,[],[f108,f34])).

fof(f108,plain,
    ( sK0 = k2_funct_1(sK1)
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f107,f27])).

fof(f107,plain,
    ( sK0 = k2_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f106,f28])).

fof(f106,plain,
    ( sK0 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f105,f24])).

fof(f24,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,
    ( sK0 = k2_funct_1(sK1)
    | k1_relat_1(sK0) != k2_relat_1(sK1)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_7 ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,
    ( ! [X0] :
        ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X0)
        | k2_funct_1(sK1) = X0
        | k1_relat_1(X0) != k2_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X0)
        | k2_funct_1(sK1) = X0
        | k1_relat_1(X0) != k2_relat_1(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f104,plain,
    ( spl2_6
    | spl2_8 ),
    inference(avatar_split_clause,[],[f100,f102,f91])).

fof(f100,plain,(
    ! [X1] :
      ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v2_funct_1(sK1) ) ),
    inference(forward_demodulation,[],[f99,f25])).

fof(f25,plain,(
    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f98,f21])).

fof(f98,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK1)
      | v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f86,f22])).

fof(f86,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK1)
      | v2_funct_1(sK1) ) ),
    inference(superposition,[],[f35,f84])).

fof(f84,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f82,f21])).

fof(f82,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f54,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f54,plain,(
    k2_relat_1(sK0) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f53,f24])).

fof(f53,plain,(
    k2_relat_1(sK0) = k10_relat_1(sK1,k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f52,f21])).

fof(f52,plain,
    ( k2_relat_1(sK0) = k10_relat_1(sK1,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f48,f27])).

fof(f48,plain,
    ( k2_relat_1(sK0) = k10_relat_1(sK1,k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f46,plain,(
    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f29,f25])).

fof(f29,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f97,plain,
    ( ~ spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f89,f95,f91])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK1)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | k2_funct_1(sK1) = X0 ) ),
    inference(forward_demodulation,[],[f88,f25])).

fof(f88,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK1)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | k2_funct_1(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f87,f21])).

fof(f87,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK1)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | k2_funct_1(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f85,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(sK1)
      | k1_relat_1(X0) != k2_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | k2_funct_1(sK1) = X0 ) ),
    inference(superposition,[],[f36,f84])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (23367)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (23376)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (23376)Refutation not found, incomplete strategy% (23376)------------------------------
% 0.22/0.47  % (23376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (23376)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (23376)Memory used [KB]: 6140
% 0.22/0.47  % (23376)Time elapsed: 0.056 s
% 0.22/0.47  % (23376)------------------------------
% 0.22/0.47  % (23376)------------------------------
% 0.22/0.47  % (23368)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (23375)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (23367)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f97,f104,f119,f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ~spl2_8),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    $false | ~spl2_8),
% 0.22/0.48    inference(subsumption_resolution,[],[f130,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ~v1_relat_1(sK0) | ~spl2_8),
% 0.22/0.48    inference(subsumption_resolution,[],[f129,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v1_funct_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_8),
% 0.22/0.48    inference(equality_resolution,[],[f103])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X1] : (k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl2_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl2_8 <=> ! [X1] : (k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ~spl2_6 | ~spl2_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f118])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    $false | (~spl2_6 | ~spl2_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f117,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ~v1_relat_1(sK1) | (~spl2_6 | ~spl2_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f116,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    sK1 != k4_relat_1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f39,f27])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    sK1 != k4_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f38,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    v2_funct_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    sK1 != k4_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f37,f28])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    sK1 != k4_relat_1(sK0) | ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.22/0.48    inference(superposition,[],[f26,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    sK1 != k2_funct_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    sK1 = k4_relat_1(sK0) | ~v1_relat_1(sK1) | (~spl2_6 | ~spl2_7)),
% 0.22/0.48    inference(superposition,[],[f31,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    sK0 = k4_relat_1(sK1) | (~spl2_6 | ~spl2_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f21])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    sK0 = k4_relat_1(sK1) | ~v1_relat_1(sK1) | (~spl2_6 | ~spl2_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f113,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    v2_funct_1(sK1) | ~spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl2_6 <=> v2_funct_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    sK0 = k4_relat_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl2_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f111,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    sK0 = k4_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl2_7),
% 0.22/0.48    inference(superposition,[],[f108,f34])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    sK0 = k2_funct_1(sK1) | ~spl2_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f107,f27])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    sK0 = k2_funct_1(sK1) | ~v1_relat_1(sK0) | ~spl2_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f106,f28])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    sK0 = k2_funct_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f105,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    sK0 = k2_funct_1(sK1) | k1_relat_1(sK0) != k2_relat_1(sK1) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl2_7),
% 0.22/0.48    inference(equality_resolution,[],[f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0] : (k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X0) | k2_funct_1(sK1) = X0 | k1_relat_1(X0) != k2_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl2_7 <=> ! [X0] : (k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X0) | k2_funct_1(sK1) = X0 | k1_relat_1(X0) != k2_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    spl2_6 | spl2_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f100,f102,f91])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X1] : (k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v2_funct_1(sK1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f99,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    k5_relat_1(sK1,sK0) = k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ( ! [X1] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v2_funct_1(sK1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f98,f21])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X1] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK1) | v2_funct_1(sK1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f86,f22])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X1] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X1) | ~v1_funct_1(sK1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK1) | v2_funct_1(sK1)) )),
% 0.22/0.48    inference(superposition,[],[f35,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f82,f21])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k1_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.22/0.48    inference(superposition,[],[f54,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f53,f24])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k10_relat_1(sK1,k1_relat_1(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f52,f21])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k10_relat_1(sK1,k1_relat_1(sK0)) | ~v1_relat_1(sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f48,f27])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k10_relat_1(sK1,k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1)),
% 0.22/0.48    inference(superposition,[],[f46,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 0.22/0.48    inference(superposition,[],[f29,f25])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ~spl2_6 | spl2_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f89,f95,f91])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0] : (k5_relat_1(sK1,sK0) != k5_relat_1(sK1,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK1) | k1_relat_1(X0) != k2_relat_1(sK1) | k2_funct_1(sK1) = X0) )),
% 0.22/0.48    inference(forward_demodulation,[],[f88,f25])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK1) | k1_relat_1(X0) != k2_relat_1(sK1) | k2_funct_1(sK1) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f87,f21])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK1) | k1_relat_1(X0) != k2_relat_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = X0) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f85,f22])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0] : (k6_relat_1(k2_relat_1(sK0)) != k5_relat_1(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(sK1) | k1_relat_1(X0) != k2_relat_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = X0) )),
% 0.22/0.48    inference(superposition,[],[f36,f84])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (23367)------------------------------
% 0.22/0.48  % (23367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23367)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (23367)Memory used [KB]: 10618
% 0.22/0.48  % (23367)Time elapsed: 0.073 s
% 0.22/0.48  % (23367)------------------------------
% 0.22/0.48  % (23367)------------------------------
% 0.22/0.49  % (23362)Success in time 0.127 s
%------------------------------------------------------------------------------
