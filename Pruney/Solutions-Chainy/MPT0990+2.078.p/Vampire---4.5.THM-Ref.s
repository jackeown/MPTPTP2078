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
% DateTime   : Thu Dec  3 13:02:41 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  275 ( 595 expanded)
%              Number of leaves         :   64 ( 259 expanded)
%              Depth                    :   16
%              Number of atoms          : 1253 (2928 expanded)
%              Number of equality atoms :  264 ( 769 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f753,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f155,f164,f169,f194,f204,f246,f258,f304,f327,f386,f388,f400,f416,f444,f495,f538,f544,f618,f687,f713,f743,f744,f745,f746,f747,f748,f752])).

fof(f752,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f748,plain,
    ( sK2 != k2_funct_1(sK3)
    | k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | sK0 != k10_relat_1(sK2,sK1)
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f747,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f746,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f745,plain,
    ( sK2 != k2_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f744,plain,
    ( k1_relat_1(sK3) != k10_relat_1(sK3,sK0)
    | sK1 != k10_relat_1(sK3,sK0)
    | sK1 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f743,plain,
    ( ~ spl4_50
    | ~ spl4_47
    | ~ spl4_55
    | spl4_56
    | ~ spl4_57
    | ~ spl4_58
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f726,f383,f351,f161,f131,f740,f736,f732,f728,f665,f696])).

fof(f696,plain,
    ( spl4_50
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f665,plain,
    ( spl4_47
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f728,plain,
    ( spl4_55
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f732,plain,
    ( spl4_56
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f736,plain,
    ( spl4_57
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f740,plain,
    ( spl4_58
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f131,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f161,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f351,plain,
    ( spl4_31
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f383,plain,
    ( spl4_35
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f726,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f725,f353])).

fof(f353,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f351])).

fof(f725,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f724,f163])).

fof(f163,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f724,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f692,f133])).

fof(f133,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f692,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_35 ),
    inference(superposition,[],[f64,f385])).

fof(f385,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f383])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
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
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f713,plain,
    ( spl4_52
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f708,f383,f362,f351,f161,f131,f710])).

fof(f710,plain,
    ( spl4_52
  <=> sK1 = k10_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f362,plain,
    ( spl4_32
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f708,plain,
    ( sK1 = k10_relat_1(sK3,sK0)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f707,f353])).

fof(f707,plain,
    ( sK1 = k10_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f706,f82])).

fof(f82,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f706,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f705,f163])).

fof(f705,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f704,f133])).

fof(f704,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f693,f364])).

fof(f364,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f362])).

fof(f693,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_35 ),
    inference(duplicate_literal_removal,[],[f689])).

fof(f689,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f207,f385])).

fof(f207,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k5_relat_1(X3,k2_funct_1(X2))) = k10_relat_1(X2,k2_relat_1(X3))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f205,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f205,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k5_relat_1(X3,k2_funct_1(X2))) = k10_relat_1(X2,k2_relat_1(X3))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f63,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f687,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | spl4_47 ),
    inference(avatar_contradiction_clause,[],[f686])).

fof(f686,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | spl4_47 ),
    inference(subsumption_resolution,[],[f685,f163])).

fof(f685,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_9
    | spl4_47 ),
    inference(subsumption_resolution,[],[f683,f133])).

fof(f683,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_47 ),
    inference(resolution,[],[f667,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f667,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f665])).

fof(f618,plain,
    ( spl4_45
    | ~ spl4_46
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f609,f450,f362,f351,f189,f166,f161,f146,f131,f615,f611])).

fof(f611,plain,
    ( spl4_45
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f615,plain,
    ( spl4_46
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f146,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f166,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f189,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f450,plain,
    ( spl4_42
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f609,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f608,f191])).

fof(f191,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f189])).

fof(f608,plain,
    ( sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(trivial_inequality_removal,[],[f607])).

fof(f607,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f606,f353])).

fof(f606,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f605,f163])).

fof(f605,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f604,f133])).

fof(f604,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f603,f168])).

fof(f168,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f166])).

fof(f603,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f602,f148])).

fof(f148,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f602,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_32
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f592,f364])).

fof(f592,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_42 ),
    inference(superposition,[],[f64,f452])).

fof(f452,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f450])).

fof(f544,plain,
    ( spl4_42
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f528,f441,f146,f136,f131,f121,f450])).

fof(f121,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f136,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f441,plain,
    ( spl4_40
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f528,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f527,f148])).

fof(f527,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f526,f138])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f526,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f525,f133])).

fof(f525,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f510,f123])).

fof(f123,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f510,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_40 ),
    inference(superposition,[],[f79,f443])).

fof(f443,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f441])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f538,plain,
    ( spl4_32
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f537,f441,f146,f141,f136,f131,f126,f121,f116,f101,f362])).

fof(f101,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f126,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f141,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f537,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f536,f133])).

fof(f536,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f535,f128])).

fof(f128,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f535,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f534,f123])).

fof(f534,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f518,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f518,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f507,f71])).

fof(f71,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f507,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(superposition,[],[f338,f443])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f337,f148])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f336,f143])).

fof(f143,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f335,f138])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f332])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(superposition,[],[f69,f118])).

fof(f118,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f495,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(subsumption_resolution,[],[f493,f148])).

fof(f493,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_39 ),
    inference(subsumption_resolution,[],[f492,f138])).

fof(f492,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_39 ),
    inference(subsumption_resolution,[],[f491,f133])).

fof(f491,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_39 ),
    inference(subsumption_resolution,[],[f488,f123])).

fof(f488,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_39 ),
    inference(resolution,[],[f439,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f439,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl4_39
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f444,plain,
    ( ~ spl4_39
    | spl4_40
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f433,f152,f441,f437])).

fof(f152,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f433,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f211,f154])).

fof(f154,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f211,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f72,f156])).

fof(f156,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f75,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f416,plain,
    ( spl4_37
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f415,f255,f166,f146,f106,f409])).

fof(f409,plain,
    ( spl4_37
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f106,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f255,plain,
    ( spl4_23
  <=> sK0 = k9_relat_1(k2_funct_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f415,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f414,f168])).

fof(f414,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f413,f148])).

fof(f413,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f404,f108])).

fof(f108,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f404,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(superposition,[],[f63,f257])).

fof(f257,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f255])).

fof(f400,plain,
    ( spl4_36
    | ~ spl4_14
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f395,f351,f161,f397])).

fof(f397,plain,
    ( spl4_36
  <=> k1_relat_1(sK3) = k10_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f395,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,sK0)
    | ~ spl4_14
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f393,f163])).

fof(f393,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_31 ),
    inference(superposition,[],[f85,f353])).

fof(f85,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f388,plain,
    ( spl4_31
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f387,f324,f121,f351])).

fof(f324,plain,
    ( spl4_30
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f387,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f344,f123])).

fof(f344,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_30 ),
    inference(superposition,[],[f80,f326])).

fof(f326,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f324])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f386,plain,
    ( spl4_35
    | ~ spl4_32
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f381,f324,f131,f126,f121,f101,f362,f383])).

fof(f381,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f380,f133])).

fof(f380,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f379,f128])).

fof(f379,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f378,f123])).

fof(f378,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f345,f103])).

fof(f345,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_30 ),
    inference(superposition,[],[f229,f326])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f61,f76])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f327,plain,
    ( spl4_30
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f322,f152,f146,f141,f136,f131,f126,f121,f324])).

fof(f322,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f321,f133])).

fof(f321,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f320,f128])).

fof(f320,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f319,f123])).

fof(f319,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f318,f148])).

fof(f318,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f317,f143])).

fof(f317,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f314,f138])).

fof(f314,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f313,f154])).

fof(f313,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f74,f76])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f304,plain,
    ( ~ spl4_12
    | ~ spl4_15
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_15
    | spl4_22 ),
    inference(subsumption_resolution,[],[f302,f168])).

fof(f302,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_12
    | spl4_22 ),
    inference(subsumption_resolution,[],[f300,f148])).

fof(f300,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_22 ),
    inference(resolution,[],[f253,f65])).

fof(f253,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_22
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f258,plain,
    ( ~ spl4_22
    | spl4_23
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f249,f243,f189,f166,f255,f251])).

fof(f243,plain,
    ( spl4_21
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f249,plain,
    ( sK0 = k9_relat_1(k2_funct_1(sK2),sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f247,f82])).

fof(f247,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK1) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_21 ),
    inference(superposition,[],[f198,f245])).

fof(f245,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f243])).

fof(f198,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(sK2,X0)) = k9_relat_1(X0,sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f196,f168])).

fof(f196,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(sK2,X0)) = k9_relat_1(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_18 ),
    inference(superposition,[],[f84,f191])).

fof(f246,plain,
    ( spl4_21
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f241,f146,f141,f136,f116,f106,f96,f243])).

fof(f96,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f241,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f240,f148])).

fof(f240,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f239,f143])).

fof(f239,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f238,f138])).

fof(f238,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f237,f108])).

fof(f237,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f236,f98])).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f236,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f233])).

fof(f233,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f229,f118])).

fof(f204,plain,
    ( spl4_19
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f199,f189,f166,f201])).

fof(f201,plain,
    ( spl4_19
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f199,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f197,f168])).

fof(f197,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f85,f191])).

fof(f194,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f193,f136,f116,f189])).

fof(f193,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f186,f138])).

fof(f186,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f118,f80])).

fof(f169,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f158,f136,f166])).

fof(f158,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f83,f138])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f164,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f157,f121,f161])).

fof(f157,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f83,f123])).

fof(f155,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f150,f111,f152])).

fof(f111,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f150,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f113,f76])).

fof(f113,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f149,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f49,f146])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f144,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f50,f141])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f139,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f51,f136])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f134,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f52,f131])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f129,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f53,f126])).

fof(f53,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f124,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f54,f121])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f55,f116])).

fof(f55,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f114,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f56,f111])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f57,f106])).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f101])).

fof(f58,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f59,f96])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f60,f91])).

fof(f91,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:49:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (8537)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (8554)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (8545)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (8557)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (8552)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (8536)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (8540)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (8543)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (8538)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (8539)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (8535)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (8560)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (8542)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (8553)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (8550)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (8562)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (8541)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (8563)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (8564)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (8548)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (8544)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (8555)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (8556)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (8559)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (8561)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (8546)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (8547)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (8551)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (8558)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (8551)Refutation not found, incomplete strategy% (8551)------------------------------
% 0.21/0.56  % (8551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8551)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8551)Memory used [KB]: 10746
% 0.21/0.56  % (8551)Time elapsed: 0.158 s
% 0.21/0.56  % (8551)------------------------------
% 0.21/0.56  % (8551)------------------------------
% 0.21/0.56  % (8549)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (8563)Refutation not found, incomplete strategy% (8563)------------------------------
% 0.21/0.57  % (8563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (8563)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (8563)Memory used [KB]: 11001
% 1.64/0.58  % (8563)Time elapsed: 0.171 s
% 1.64/0.58  % (8563)------------------------------
% 1.64/0.58  % (8563)------------------------------
% 1.64/0.59  % (8556)Refutation found. Thanks to Tanya!
% 1.64/0.59  % SZS status Theorem for theBenchmark
% 1.81/0.61  % SZS output start Proof for theBenchmark
% 1.81/0.61  fof(f753,plain,(
% 1.81/0.61    $false),
% 1.81/0.61    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f155,f164,f169,f194,f204,f246,f258,f304,f327,f386,f388,f400,f416,f444,f495,f538,f544,f618,f687,f713,f743,f744,f745,f746,f747,f748,f752])).
% 1.81/0.61  fof(f752,plain,(
% 1.81/0.61    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | k2_funct_1(sK2) = sK3),
% 1.81/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.81/0.61  fof(f748,plain,(
% 1.81/0.61    sK2 != k2_funct_1(sK3) | k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | sK0 != k10_relat_1(sK2,sK1) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.81/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.81/0.61  fof(f747,plain,(
% 1.81/0.61    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.81/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.81/0.61  fof(f746,plain,(
% 1.81/0.61    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 1.81/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.81/0.61  fof(f745,plain,(
% 1.81/0.61    sK2 != k2_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK2)),
% 1.81/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.81/0.61  fof(f744,plain,(
% 1.81/0.61    k1_relat_1(sK3) != k10_relat_1(sK3,sK0) | sK1 != k10_relat_1(sK3,sK0) | sK1 = k1_relat_1(sK3)),
% 1.81/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.81/0.61  fof(f743,plain,(
% 1.81/0.61    ~spl4_50 | ~spl4_47 | ~spl4_55 | spl4_56 | ~spl4_57 | ~spl4_58 | ~spl4_9 | ~spl4_14 | ~spl4_31 | ~spl4_35),
% 1.81/0.61    inference(avatar_split_clause,[],[f726,f383,f351,f161,f131,f740,f736,f732,f728,f665,f696])).
% 1.81/0.61  fof(f696,plain,(
% 1.81/0.61    spl4_50 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.81/0.61  fof(f665,plain,(
% 1.81/0.61    spl4_47 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.81/0.61  fof(f728,plain,(
% 1.81/0.61    spl4_55 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.81/0.61  fof(f732,plain,(
% 1.81/0.61    spl4_56 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.81/0.61  fof(f736,plain,(
% 1.81/0.61    spl4_57 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.81/0.61  fof(f740,plain,(
% 1.81/0.61    spl4_58 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.81/0.61  fof(f131,plain,(
% 1.81/0.61    spl4_9 <=> v1_funct_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.81/0.61  fof(f161,plain,(
% 1.81/0.61    spl4_14 <=> v1_relat_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.81/0.61  fof(f351,plain,(
% 1.81/0.61    spl4_31 <=> sK0 = k2_relat_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.81/0.61  fof(f383,plain,(
% 1.81/0.61    spl4_35 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.81/0.61  fof(f726,plain,(
% 1.81/0.61    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_31 | ~spl4_35)),
% 1.81/0.61    inference(forward_demodulation,[],[f725,f353])).
% 1.81/0.61  fof(f353,plain,(
% 1.81/0.61    sK0 = k2_relat_1(sK3) | ~spl4_31),
% 1.81/0.61    inference(avatar_component_clause,[],[f351])).
% 1.81/0.61  fof(f725,plain,(
% 1.81/0.61    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_35)),
% 1.81/0.61    inference(subsumption_resolution,[],[f724,f163])).
% 1.81/0.61  fof(f163,plain,(
% 1.81/0.61    v1_relat_1(sK3) | ~spl4_14),
% 1.81/0.61    inference(avatar_component_clause,[],[f161])).
% 1.81/0.61  fof(f724,plain,(
% 1.81/0.61    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_35)),
% 1.81/0.61    inference(subsumption_resolution,[],[f692,f133])).
% 1.81/0.61  fof(f133,plain,(
% 1.81/0.61    v1_funct_1(sK3) | ~spl4_9),
% 1.81/0.61    inference(avatar_component_clause,[],[f131])).
% 1.81/0.61  fof(f692,plain,(
% 1.81/0.61    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_35),
% 1.81/0.61    inference(superposition,[],[f64,f385])).
% 1.81/0.61  fof(f385,plain,(
% 1.81/0.61    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_35),
% 1.81/0.61    inference(avatar_component_clause,[],[f383])).
% 1.81/0.61  fof(f64,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f28])).
% 1.81/0.61  fof(f28,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.61    inference(flattening,[],[f27])).
% 1.81/0.61  fof(f27,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f7])).
% 1.81/0.61  fof(f7,axiom,(
% 1.81/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.81/0.61  fof(f713,plain,(
% 1.81/0.61    spl4_52 | ~spl4_9 | ~spl4_14 | ~spl4_31 | ~spl4_32 | ~spl4_35),
% 1.81/0.61    inference(avatar_split_clause,[],[f708,f383,f362,f351,f161,f131,f710])).
% 1.81/0.61  fof(f710,plain,(
% 1.81/0.61    spl4_52 <=> sK1 = k10_relat_1(sK3,sK0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.81/0.61  fof(f362,plain,(
% 1.81/0.61    spl4_32 <=> v2_funct_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.81/0.61  fof(f708,plain,(
% 1.81/0.61    sK1 = k10_relat_1(sK3,sK0) | (~spl4_9 | ~spl4_14 | ~spl4_31 | ~spl4_32 | ~spl4_35)),
% 1.81/0.61    inference(forward_demodulation,[],[f707,f353])).
% 1.81/0.61  fof(f707,plain,(
% 1.81/0.61    sK1 = k10_relat_1(sK3,k2_relat_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_35)),
% 1.81/0.61    inference(forward_demodulation,[],[f706,f82])).
% 1.81/0.61  fof(f82,plain,(
% 1.81/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f3])).
% 1.81/0.61  fof(f3,axiom,(
% 1.81/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.81/0.61  fof(f706,plain,(
% 1.81/0.61    k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1)) | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_35)),
% 1.81/0.61    inference(subsumption_resolution,[],[f705,f163])).
% 1.81/0.61  fof(f705,plain,(
% 1.81/0.61    k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_32 | ~spl4_35)),
% 1.81/0.61    inference(subsumption_resolution,[],[f704,f133])).
% 1.81/0.61  fof(f704,plain,(
% 1.81/0.61    k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_32 | ~spl4_35)),
% 1.81/0.61    inference(subsumption_resolution,[],[f693,f364])).
% 1.81/0.61  fof(f364,plain,(
% 1.81/0.61    v2_funct_1(sK3) | ~spl4_32),
% 1.81/0.61    inference(avatar_component_clause,[],[f362])).
% 1.81/0.61  fof(f693,plain,(
% 1.81/0.61    k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_35),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f689])).
% 1.81/0.61  fof(f689,plain,(
% 1.81/0.61    k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_35),
% 1.81/0.61    inference(superposition,[],[f207,f385])).
% 1.81/0.61  fof(f207,plain,(
% 1.81/0.61    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(X3,k2_funct_1(X2))) = k10_relat_1(X2,k2_relat_1(X3)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X3)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f205,f65])).
% 1.81/0.61  fof(f65,plain,(
% 1.81/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f30])).
% 1.81/0.61  fof(f30,plain,(
% 1.81/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.61    inference(flattening,[],[f29])).
% 1.81/0.61  fof(f29,plain,(
% 1.81/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f4])).
% 1.81/0.61  fof(f4,axiom,(
% 1.81/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.81/0.61  fof(f205,plain,(
% 1.81/0.61    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(X3,k2_funct_1(X2))) = k10_relat_1(X2,k2_relat_1(X3)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(X2)) | ~v1_relat_1(X3)) )),
% 1.81/0.61    inference(superposition,[],[f63,f84])).
% 1.81/0.61  fof(f84,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f43])).
% 1.81/0.61  fof(f43,plain,(
% 1.81/0.61    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f1])).
% 1.81/0.61  fof(f1,axiom,(
% 1.81/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.81/0.61  fof(f63,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f26])).
% 1.81/0.61  fof(f26,plain,(
% 1.81/0.61    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.81/0.61    inference(flattening,[],[f25])).
% 1.81/0.61  fof(f25,plain,(
% 1.81/0.61    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.81/0.61    inference(ennf_transformation,[],[f5])).
% 1.81/0.61  fof(f5,axiom,(
% 1.81/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.81/0.61  fof(f687,plain,(
% 1.81/0.61    ~spl4_9 | ~spl4_14 | spl4_47),
% 1.81/0.61    inference(avatar_contradiction_clause,[],[f686])).
% 1.81/0.61  fof(f686,plain,(
% 1.81/0.61    $false | (~spl4_9 | ~spl4_14 | spl4_47)),
% 1.81/0.61    inference(subsumption_resolution,[],[f685,f163])).
% 1.81/0.61  fof(f685,plain,(
% 1.81/0.61    ~v1_relat_1(sK3) | (~spl4_9 | spl4_47)),
% 1.81/0.61    inference(subsumption_resolution,[],[f683,f133])).
% 1.81/0.61  fof(f683,plain,(
% 1.81/0.61    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_47),
% 1.81/0.61    inference(resolution,[],[f667,f66])).
% 1.81/0.61  fof(f66,plain,(
% 1.81/0.61    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f30])).
% 1.81/0.61  fof(f667,plain,(
% 1.81/0.61    ~v1_funct_1(k2_funct_1(sK3)) | spl4_47),
% 1.81/0.61    inference(avatar_component_clause,[],[f665])).
% 1.81/0.61  fof(f618,plain,(
% 1.81/0.61    spl4_45 | ~spl4_46 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_31 | ~spl4_32 | ~spl4_42),
% 1.81/0.61    inference(avatar_split_clause,[],[f609,f450,f362,f351,f189,f166,f161,f146,f131,f615,f611])).
% 1.81/0.61  fof(f611,plain,(
% 1.81/0.61    spl4_45 <=> sK2 = k2_funct_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.81/0.61  fof(f615,plain,(
% 1.81/0.61    spl4_46 <=> sK1 = k1_relat_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.81/0.61  fof(f146,plain,(
% 1.81/0.61    spl4_12 <=> v1_funct_1(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.81/0.61  fof(f166,plain,(
% 1.81/0.61    spl4_15 <=> v1_relat_1(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.81/0.61  fof(f189,plain,(
% 1.81/0.61    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.81/0.61  fof(f450,plain,(
% 1.81/0.61    spl4_42 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.81/0.61  fof(f609,plain,(
% 1.81/0.61    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_31 | ~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(forward_demodulation,[],[f608,f191])).
% 1.81/0.61  fof(f191,plain,(
% 1.81/0.61    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 1.81/0.61    inference(avatar_component_clause,[],[f189])).
% 1.81/0.61  fof(f608,plain,(
% 1.81/0.61    sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_31 | ~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(trivial_inequality_removal,[],[f607])).
% 1.81/0.61  fof(f607,plain,(
% 1.81/0.61    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_31 | ~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(forward_demodulation,[],[f606,f353])).
% 1.81/0.61  fof(f606,plain,(
% 1.81/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(subsumption_resolution,[],[f605,f163])).
% 1.81/0.61  fof(f605,plain,(
% 1.81/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(subsumption_resolution,[],[f604,f133])).
% 1.81/0.61  fof(f604,plain,(
% 1.81/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(subsumption_resolution,[],[f603,f168])).
% 1.81/0.61  fof(f168,plain,(
% 1.81/0.61    v1_relat_1(sK2) | ~spl4_15),
% 1.81/0.61    inference(avatar_component_clause,[],[f166])).
% 1.81/0.61  fof(f603,plain,(
% 1.81/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(subsumption_resolution,[],[f602,f148])).
% 1.81/0.61  fof(f148,plain,(
% 1.81/0.61    v1_funct_1(sK2) | ~spl4_12),
% 1.81/0.61    inference(avatar_component_clause,[],[f146])).
% 1.81/0.61  fof(f602,plain,(
% 1.81/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_32 | ~spl4_42)),
% 1.81/0.61    inference(subsumption_resolution,[],[f592,f364])).
% 1.81/0.61  fof(f592,plain,(
% 1.81/0.61    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_42),
% 1.81/0.61    inference(superposition,[],[f64,f452])).
% 1.81/0.61  fof(f452,plain,(
% 1.81/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_42),
% 1.81/0.61    inference(avatar_component_clause,[],[f450])).
% 1.81/0.61  fof(f544,plain,(
% 1.81/0.61    spl4_42 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_40),
% 1.81/0.61    inference(avatar_split_clause,[],[f528,f441,f146,f136,f131,f121,f450])).
% 1.81/0.61  fof(f121,plain,(
% 1.81/0.61    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.81/0.61  fof(f136,plain,(
% 1.81/0.61    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.81/0.61  fof(f441,plain,(
% 1.81/0.61    spl4_40 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.81/0.61  fof(f528,plain,(
% 1.81/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f527,f148])).
% 1.81/0.61  fof(f527,plain,(
% 1.81/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f526,f138])).
% 1.81/0.61  fof(f138,plain,(
% 1.81/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.81/0.61    inference(avatar_component_clause,[],[f136])).
% 1.81/0.61  fof(f526,plain,(
% 1.81/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f525,f133])).
% 1.81/0.61  fof(f525,plain,(
% 1.81/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f510,f123])).
% 1.81/0.61  fof(f123,plain,(
% 1.81/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.81/0.61    inference(avatar_component_clause,[],[f121])).
% 1.81/0.61  fof(f510,plain,(
% 1.81/0.61    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_40),
% 1.81/0.61    inference(superposition,[],[f79,f443])).
% 1.81/0.61  fof(f443,plain,(
% 1.81/0.61    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_40),
% 1.81/0.61    inference(avatar_component_clause,[],[f441])).
% 1.81/0.61  fof(f79,plain,(
% 1.81/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f40])).
% 1.81/0.61  fof(f40,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.81/0.61    inference(flattening,[],[f39])).
% 1.81/0.61  fof(f39,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.81/0.61    inference(ennf_transformation,[],[f13])).
% 1.81/0.61  fof(f13,axiom,(
% 1.81/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.81/0.61  fof(f538,plain,(
% 1.81/0.61    spl4_32 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40),
% 1.81/0.61    inference(avatar_split_clause,[],[f537,f441,f146,f141,f136,f131,f126,f121,f116,f101,f362])).
% 1.81/0.61  fof(f101,plain,(
% 1.81/0.61    spl4_3 <=> k1_xboole_0 = sK0),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.81/0.61  fof(f116,plain,(
% 1.81/0.61    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.81/0.61  fof(f126,plain,(
% 1.81/0.61    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.81/0.61  fof(f141,plain,(
% 1.81/0.61    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.81/0.61  fof(f537,plain,(
% 1.81/0.61    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f536,f133])).
% 1.81/0.61  fof(f536,plain,(
% 1.81/0.61    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f535,f128])).
% 1.81/0.61  fof(f128,plain,(
% 1.81/0.61    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.81/0.61    inference(avatar_component_clause,[],[f126])).
% 1.81/0.61  fof(f535,plain,(
% 1.81/0.61    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f534,f123])).
% 1.81/0.61  fof(f534,plain,(
% 1.81/0.61    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f518,f103])).
% 1.81/0.61  fof(f103,plain,(
% 1.81/0.61    k1_xboole_0 != sK0 | spl4_3),
% 1.81/0.61    inference(avatar_component_clause,[],[f101])).
% 1.81/0.61  fof(f518,plain,(
% 1.81/0.61    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.81/0.61    inference(subsumption_resolution,[],[f507,f71])).
% 1.81/0.61  fof(f71,plain,(
% 1.81/0.61    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f6])).
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.81/0.61  fof(f507,plain,(
% 1.81/0.61    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 1.81/0.61    inference(superposition,[],[f338,f443])).
% 1.81/0.61  fof(f338,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.81/0.61    inference(subsumption_resolution,[],[f337,f148])).
% 1.81/0.61  fof(f337,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.81/0.61    inference(subsumption_resolution,[],[f336,f143])).
% 1.81/0.61  fof(f143,plain,(
% 1.81/0.61    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.81/0.61    inference(avatar_component_clause,[],[f141])).
% 1.81/0.61  fof(f336,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.81/0.61    inference(subsumption_resolution,[],[f335,f138])).
% 1.81/0.61  fof(f335,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.81/0.61    inference(trivial_inequality_removal,[],[f332])).
% 1.81/0.61  fof(f332,plain,(
% 1.81/0.61    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.81/0.61    inference(superposition,[],[f69,f118])).
% 1.81/0.61  fof(f118,plain,(
% 1.81/0.61    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.81/0.61    inference(avatar_component_clause,[],[f116])).
% 1.81/0.61  fof(f69,plain,(
% 1.81/0.61    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f32])).
% 1.81/0.61  fof(f32,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.81/0.61    inference(flattening,[],[f31])).
% 1.81/0.61  fof(f31,plain,(
% 1.81/0.61    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.81/0.61    inference(ennf_transformation,[],[f16])).
% 1.81/0.61  fof(f16,axiom,(
% 1.81/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.81/0.62  fof(f495,plain,(
% 1.81/0.62    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39),
% 1.81/0.62    inference(avatar_contradiction_clause,[],[f494])).
% 1.81/0.62  fof(f494,plain,(
% 1.81/0.62    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39)),
% 1.81/0.62    inference(subsumption_resolution,[],[f493,f148])).
% 1.81/0.62  fof(f493,plain,(
% 1.81/0.62    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_39)),
% 1.81/0.62    inference(subsumption_resolution,[],[f492,f138])).
% 1.81/0.62  fof(f492,plain,(
% 1.81/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_39)),
% 1.81/0.62    inference(subsumption_resolution,[],[f491,f133])).
% 1.81/0.62  fof(f491,plain,(
% 1.81/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_39)),
% 1.81/0.62    inference(subsumption_resolution,[],[f488,f123])).
% 1.81/0.62  fof(f488,plain,(
% 1.81/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_39),
% 1.81/0.62    inference(resolution,[],[f439,f78])).
% 1.81/0.62  fof(f78,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f38])).
% 1.81/0.62  fof(f38,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.81/0.62    inference(flattening,[],[f37])).
% 1.81/0.62  fof(f37,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.81/0.62    inference(ennf_transformation,[],[f11])).
% 1.81/0.62  fof(f11,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.81/0.62  fof(f439,plain,(
% 1.81/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_39),
% 1.81/0.62    inference(avatar_component_clause,[],[f437])).
% 1.81/0.62  fof(f437,plain,(
% 1.81/0.62    spl4_39 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.81/0.62  fof(f444,plain,(
% 1.81/0.62    ~spl4_39 | spl4_40 | ~spl4_13),
% 1.81/0.62    inference(avatar_split_clause,[],[f433,f152,f441,f437])).
% 1.81/0.62  fof(f152,plain,(
% 1.81/0.62    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.81/0.62  fof(f433,plain,(
% 1.81/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.81/0.62    inference(resolution,[],[f211,f154])).
% 1.81/0.62  fof(f154,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.81/0.62    inference(avatar_component_clause,[],[f152])).
% 1.81/0.62  fof(f211,plain,(
% 1.81/0.62    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.81/0.62    inference(resolution,[],[f72,f156])).
% 1.81/0.62  fof(f156,plain,(
% 1.81/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f75,f76])).
% 1.81/0.62  fof(f76,plain,(
% 1.81/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f14])).
% 1.81/0.62  fof(f14,axiom,(
% 1.81/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.81/0.62  fof(f75,plain,(
% 1.81/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f20])).
% 1.81/0.62  fof(f20,plain,(
% 1.81/0.62    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.81/0.62    inference(pure_predicate_removal,[],[f12])).
% 1.81/0.62  fof(f12,axiom,(
% 1.81/0.62    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.81/0.62  fof(f72,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f48])).
% 1.81/0.62  fof(f48,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(nnf_transformation,[],[f34])).
% 1.81/0.62  fof(f34,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(flattening,[],[f33])).
% 1.81/0.62  fof(f33,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.81/0.62    inference(ennf_transformation,[],[f10])).
% 1.81/0.62  fof(f10,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.81/0.62  fof(f416,plain,(
% 1.81/0.62    spl4_37 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_23),
% 1.81/0.62    inference(avatar_split_clause,[],[f415,f255,f166,f146,f106,f409])).
% 1.81/0.62  fof(f409,plain,(
% 1.81/0.62    spl4_37 <=> sK0 = k10_relat_1(sK2,sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.81/0.62  fof(f106,plain,(
% 1.81/0.62    spl4_4 <=> v2_funct_1(sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.81/0.62  fof(f255,plain,(
% 1.81/0.62    spl4_23 <=> sK0 = k9_relat_1(k2_funct_1(sK2),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.81/0.62  fof(f415,plain,(
% 1.81/0.62    sK0 = k10_relat_1(sK2,sK1) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_23)),
% 1.81/0.62    inference(subsumption_resolution,[],[f414,f168])).
% 1.81/0.62  fof(f414,plain,(
% 1.81/0.62    sK0 = k10_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_23)),
% 1.81/0.62    inference(subsumption_resolution,[],[f413,f148])).
% 1.81/0.62  fof(f413,plain,(
% 1.81/0.62    sK0 = k10_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_23)),
% 1.81/0.62    inference(subsumption_resolution,[],[f404,f108])).
% 1.81/0.62  fof(f108,plain,(
% 1.81/0.62    v2_funct_1(sK2) | ~spl4_4),
% 1.81/0.62    inference(avatar_component_clause,[],[f106])).
% 1.81/0.62  fof(f404,plain,(
% 1.81/0.62    sK0 = k10_relat_1(sK2,sK1) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_23),
% 1.81/0.62    inference(superposition,[],[f63,f257])).
% 1.81/0.62  fof(f257,plain,(
% 1.81/0.62    sK0 = k9_relat_1(k2_funct_1(sK2),sK1) | ~spl4_23),
% 1.81/0.62    inference(avatar_component_clause,[],[f255])).
% 1.81/0.62  fof(f400,plain,(
% 1.81/0.62    spl4_36 | ~spl4_14 | ~spl4_31),
% 1.81/0.62    inference(avatar_split_clause,[],[f395,f351,f161,f397])).
% 1.81/0.62  fof(f397,plain,(
% 1.81/0.62    spl4_36 <=> k1_relat_1(sK3) = k10_relat_1(sK3,sK0)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.81/0.62  fof(f395,plain,(
% 1.81/0.62    k1_relat_1(sK3) = k10_relat_1(sK3,sK0) | (~spl4_14 | ~spl4_31)),
% 1.81/0.62    inference(subsumption_resolution,[],[f393,f163])).
% 1.81/0.62  fof(f393,plain,(
% 1.81/0.62    k1_relat_1(sK3) = k10_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_31),
% 1.81/0.62    inference(superposition,[],[f85,f353])).
% 1.81/0.62  fof(f85,plain,(
% 1.81/0.62    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f44])).
% 1.81/0.62  fof(f44,plain,(
% 1.81/0.62    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f2])).
% 1.81/0.62  fof(f2,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.81/0.62  fof(f388,plain,(
% 1.81/0.62    spl4_31 | ~spl4_7 | ~spl4_30),
% 1.81/0.62    inference(avatar_split_clause,[],[f387,f324,f121,f351])).
% 1.81/0.62  fof(f324,plain,(
% 1.81/0.62    spl4_30 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.81/0.62  fof(f387,plain,(
% 1.81/0.62    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_30)),
% 1.81/0.62    inference(subsumption_resolution,[],[f344,f123])).
% 1.81/0.62  fof(f344,plain,(
% 1.81/0.62    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_30),
% 1.81/0.62    inference(superposition,[],[f80,f326])).
% 1.81/0.62  fof(f326,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_30),
% 1.81/0.62    inference(avatar_component_clause,[],[f324])).
% 1.81/0.62  fof(f80,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f41])).
% 1.81/0.62  fof(f41,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(ennf_transformation,[],[f9])).
% 1.81/0.62  fof(f9,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.81/0.62  fof(f386,plain,(
% 1.81/0.62    spl4_35 | ~spl4_32 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_30),
% 1.81/0.62    inference(avatar_split_clause,[],[f381,f324,f131,f126,f121,f101,f362,f383])).
% 1.81/0.62  fof(f381,plain,(
% 1.81/0.62    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_30)),
% 1.81/0.62    inference(subsumption_resolution,[],[f380,f133])).
% 1.81/0.62  fof(f380,plain,(
% 1.81/0.62    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_30)),
% 1.81/0.62    inference(subsumption_resolution,[],[f379,f128])).
% 1.81/0.62  fof(f379,plain,(
% 1.81/0.62    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_30)),
% 1.81/0.62    inference(subsumption_resolution,[],[f378,f123])).
% 1.81/0.62  fof(f378,plain,(
% 1.81/0.62    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_30)),
% 1.81/0.62    inference(subsumption_resolution,[],[f345,f103])).
% 1.81/0.62  fof(f345,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_30),
% 1.81/0.62    inference(trivial_inequality_removal,[],[f343])).
% 1.81/0.62  fof(f343,plain,(
% 1.81/0.62    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_30),
% 1.81/0.62    inference(superposition,[],[f229,f326])).
% 1.81/0.62  fof(f229,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/0.62    inference(forward_demodulation,[],[f61,f76])).
% 1.81/0.62  fof(f61,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f24])).
% 1.81/0.62  fof(f24,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.81/0.62    inference(flattening,[],[f23])).
% 1.81/0.62  fof(f23,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.81/0.62    inference(ennf_transformation,[],[f17])).
% 1.81/0.62  fof(f17,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.81/0.62  fof(f327,plain,(
% 1.81/0.62    spl4_30 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.81/0.62    inference(avatar_split_clause,[],[f322,f152,f146,f141,f136,f131,f126,f121,f324])).
% 1.81/0.62  fof(f322,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.81/0.62    inference(subsumption_resolution,[],[f321,f133])).
% 1.81/0.62  fof(f321,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.81/0.62    inference(subsumption_resolution,[],[f320,f128])).
% 1.81/0.62  fof(f320,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.81/0.62    inference(subsumption_resolution,[],[f319,f123])).
% 1.81/0.62  fof(f319,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.81/0.62    inference(subsumption_resolution,[],[f318,f148])).
% 1.81/0.62  fof(f318,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.81/0.62    inference(subsumption_resolution,[],[f317,f143])).
% 1.81/0.62  fof(f317,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 1.81/0.62    inference(subsumption_resolution,[],[f314,f138])).
% 1.81/0.62  fof(f314,plain,(
% 1.81/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 1.81/0.62    inference(resolution,[],[f313,f154])).
% 1.81/0.62  fof(f313,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/0.62    inference(forward_demodulation,[],[f74,f76])).
% 1.81/0.62  fof(f74,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f36])).
% 1.81/0.62  fof(f36,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.81/0.62    inference(flattening,[],[f35])).
% 1.81/0.62  fof(f35,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.81/0.62    inference(ennf_transformation,[],[f15])).
% 1.81/0.62  fof(f15,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.81/0.62  fof(f304,plain,(
% 1.81/0.62    ~spl4_12 | ~spl4_15 | spl4_22),
% 1.81/0.62    inference(avatar_contradiction_clause,[],[f303])).
% 1.81/0.62  fof(f303,plain,(
% 1.81/0.62    $false | (~spl4_12 | ~spl4_15 | spl4_22)),
% 1.81/0.62    inference(subsumption_resolution,[],[f302,f168])).
% 1.81/0.62  fof(f302,plain,(
% 1.81/0.62    ~v1_relat_1(sK2) | (~spl4_12 | spl4_22)),
% 1.81/0.62    inference(subsumption_resolution,[],[f300,f148])).
% 1.81/0.62  fof(f300,plain,(
% 1.81/0.62    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_22),
% 1.81/0.62    inference(resolution,[],[f253,f65])).
% 1.81/0.62  fof(f253,plain,(
% 1.81/0.62    ~v1_relat_1(k2_funct_1(sK2)) | spl4_22),
% 1.81/0.62    inference(avatar_component_clause,[],[f251])).
% 1.81/0.62  fof(f251,plain,(
% 1.81/0.62    spl4_22 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.81/0.62  fof(f258,plain,(
% 1.81/0.62    ~spl4_22 | spl4_23 | ~spl4_15 | ~spl4_18 | ~spl4_21),
% 1.81/0.62    inference(avatar_split_clause,[],[f249,f243,f189,f166,f255,f251])).
% 1.81/0.62  fof(f243,plain,(
% 1.81/0.62    spl4_21 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.81/0.62  fof(f249,plain,(
% 1.81/0.62    sK0 = k9_relat_1(k2_funct_1(sK2),sK1) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_15 | ~spl4_18 | ~spl4_21)),
% 1.81/0.62    inference(forward_demodulation,[],[f247,f82])).
% 1.81/0.62  fof(f247,plain,(
% 1.81/0.62    k9_relat_1(k2_funct_1(sK2),sK1) = k2_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_15 | ~spl4_18 | ~spl4_21)),
% 1.81/0.62    inference(superposition,[],[f198,f245])).
% 1.81/0.62  fof(f245,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_21),
% 1.81/0.62    inference(avatar_component_clause,[],[f243])).
% 1.81/0.62  fof(f198,plain,(
% 1.81/0.62    ( ! [X0] : (k2_relat_1(k5_relat_1(sK2,X0)) = k9_relat_1(X0,sK1) | ~v1_relat_1(X0)) ) | (~spl4_15 | ~spl4_18)),
% 1.81/0.62    inference(subsumption_resolution,[],[f196,f168])).
% 1.81/0.62  fof(f196,plain,(
% 1.81/0.62    ( ! [X0] : (k2_relat_1(k5_relat_1(sK2,X0)) = k9_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | ~spl4_18),
% 1.81/0.62    inference(superposition,[],[f84,f191])).
% 1.81/0.62  fof(f246,plain,(
% 1.81/0.62    spl4_21 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.81/0.62    inference(avatar_split_clause,[],[f241,f146,f141,f136,f116,f106,f96,f243])).
% 1.81/0.62  fof(f96,plain,(
% 1.81/0.62    spl4_2 <=> k1_xboole_0 = sK1),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.81/0.62  fof(f241,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.81/0.62    inference(subsumption_resolution,[],[f240,f148])).
% 1.81/0.62  fof(f240,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.81/0.62    inference(subsumption_resolution,[],[f239,f143])).
% 1.81/0.62  fof(f239,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.81/0.62    inference(subsumption_resolution,[],[f238,f138])).
% 1.81/0.62  fof(f238,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.81/0.62    inference(subsumption_resolution,[],[f237,f108])).
% 1.81/0.62  fof(f237,plain,(
% 1.81/0.62    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.81/0.62    inference(subsumption_resolution,[],[f236,f98])).
% 1.81/0.62  fof(f98,plain,(
% 1.81/0.62    k1_xboole_0 != sK1 | spl4_2),
% 1.81/0.62    inference(avatar_component_clause,[],[f96])).
% 1.81/0.62  fof(f236,plain,(
% 1.81/0.62    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.81/0.62    inference(trivial_inequality_removal,[],[f233])).
% 1.81/0.62  fof(f233,plain,(
% 1.81/0.62    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.81/0.62    inference(superposition,[],[f229,f118])).
% 1.81/0.62  fof(f204,plain,(
% 1.81/0.62    spl4_19 | ~spl4_15 | ~spl4_18),
% 1.81/0.62    inference(avatar_split_clause,[],[f199,f189,f166,f201])).
% 1.81/0.62  fof(f201,plain,(
% 1.81/0.62    spl4_19 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.81/0.62  fof(f199,plain,(
% 1.81/0.62    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | (~spl4_15 | ~spl4_18)),
% 1.81/0.62    inference(subsumption_resolution,[],[f197,f168])).
% 1.81/0.62  fof(f197,plain,(
% 1.81/0.62    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl4_18),
% 1.81/0.62    inference(superposition,[],[f85,f191])).
% 1.81/0.62  fof(f194,plain,(
% 1.81/0.62    spl4_18 | ~spl4_6 | ~spl4_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f193,f136,f116,f189])).
% 1.81/0.62  fof(f193,plain,(
% 1.81/0.62    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 1.81/0.62    inference(subsumption_resolution,[],[f186,f138])).
% 1.81/0.62  fof(f186,plain,(
% 1.81/0.62    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 1.81/0.62    inference(superposition,[],[f118,f80])).
% 1.81/0.62  fof(f169,plain,(
% 1.81/0.62    spl4_15 | ~spl4_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f158,f136,f166])).
% 1.81/0.62  fof(f158,plain,(
% 1.81/0.62    v1_relat_1(sK2) | ~spl4_10),
% 1.81/0.62    inference(resolution,[],[f83,f138])).
% 1.81/0.62  fof(f83,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f42])).
% 1.81/0.62  fof(f42,plain,(
% 1.81/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(ennf_transformation,[],[f8])).
% 1.81/0.62  fof(f8,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.81/0.62  fof(f164,plain,(
% 1.81/0.62    spl4_14 | ~spl4_7),
% 1.81/0.62    inference(avatar_split_clause,[],[f157,f121,f161])).
% 1.81/0.62  fof(f157,plain,(
% 1.81/0.62    v1_relat_1(sK3) | ~spl4_7),
% 1.81/0.62    inference(resolution,[],[f83,f123])).
% 1.81/0.62  fof(f155,plain,(
% 1.81/0.62    spl4_13 | ~spl4_5),
% 1.81/0.62    inference(avatar_split_clause,[],[f150,f111,f152])).
% 1.81/0.62  fof(f111,plain,(
% 1.81/0.62    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.81/0.62  fof(f150,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.81/0.62    inference(backward_demodulation,[],[f113,f76])).
% 1.81/0.62  fof(f113,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.81/0.62    inference(avatar_component_clause,[],[f111])).
% 1.81/0.62  fof(f149,plain,(
% 1.81/0.62    spl4_12),
% 1.81/0.62    inference(avatar_split_clause,[],[f49,f146])).
% 1.81/0.62  fof(f49,plain,(
% 1.81/0.62    v1_funct_1(sK2)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f47,plain,(
% 1.81/0.62    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f46,f45])).
% 1.81/0.62  fof(f45,plain,(
% 1.81/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f46,plain,(
% 1.81/0.62    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f22,plain,(
% 1.81/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.81/0.62    inference(flattening,[],[f21])).
% 1.81/0.62  fof(f21,plain,(
% 1.81/0.62    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.81/0.62    inference(ennf_transformation,[],[f19])).
% 1.81/0.62  fof(f19,negated_conjecture,(
% 1.81/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.81/0.62    inference(negated_conjecture,[],[f18])).
% 1.81/0.62  fof(f18,conjecture,(
% 1.81/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.81/0.62  fof(f144,plain,(
% 1.81/0.62    spl4_11),
% 1.81/0.62    inference(avatar_split_clause,[],[f50,f141])).
% 1.81/0.62  fof(f50,plain,(
% 1.81/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f139,plain,(
% 1.81/0.62    spl4_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f51,f136])).
% 1.81/0.62  fof(f51,plain,(
% 1.81/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f134,plain,(
% 1.81/0.62    spl4_9),
% 1.81/0.62    inference(avatar_split_clause,[],[f52,f131])).
% 1.81/0.62  fof(f52,plain,(
% 1.81/0.62    v1_funct_1(sK3)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f129,plain,(
% 1.81/0.62    spl4_8),
% 1.81/0.62    inference(avatar_split_clause,[],[f53,f126])).
% 1.81/0.62  fof(f53,plain,(
% 1.81/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f124,plain,(
% 1.81/0.62    spl4_7),
% 1.81/0.62    inference(avatar_split_clause,[],[f54,f121])).
% 1.81/0.62  fof(f54,plain,(
% 1.81/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f119,plain,(
% 1.81/0.62    spl4_6),
% 1.81/0.62    inference(avatar_split_clause,[],[f55,f116])).
% 1.81/0.62  fof(f55,plain,(
% 1.81/0.62    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f114,plain,(
% 1.81/0.62    spl4_5),
% 1.81/0.62    inference(avatar_split_clause,[],[f56,f111])).
% 1.81/0.62  fof(f56,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f109,plain,(
% 1.81/0.62    spl4_4),
% 1.81/0.62    inference(avatar_split_clause,[],[f57,f106])).
% 1.81/0.62  fof(f57,plain,(
% 1.81/0.62    v2_funct_1(sK2)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f104,plain,(
% 1.81/0.62    ~spl4_3),
% 1.81/0.62    inference(avatar_split_clause,[],[f58,f101])).
% 1.81/0.62  fof(f58,plain,(
% 1.81/0.62    k1_xboole_0 != sK0),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f99,plain,(
% 1.81/0.62    ~spl4_2),
% 1.81/0.62    inference(avatar_split_clause,[],[f59,f96])).
% 1.81/0.62  fof(f59,plain,(
% 1.81/0.62    k1_xboole_0 != sK1),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f94,plain,(
% 1.81/0.62    ~spl4_1),
% 1.81/0.62    inference(avatar_split_clause,[],[f60,f91])).
% 1.81/0.62  fof(f91,plain,(
% 1.81/0.62    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.81/0.62  fof(f60,plain,(
% 1.81/0.62    k2_funct_1(sK2) != sK3),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  % SZS output end Proof for theBenchmark
% 1.81/0.62  % (8556)------------------------------
% 1.81/0.62  % (8556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (8556)Termination reason: Refutation
% 1.81/0.62  
% 1.81/0.62  % (8556)Memory used [KB]: 6908
% 1.81/0.62  % (8556)Time elapsed: 0.196 s
% 1.81/0.62  % (8556)------------------------------
% 1.81/0.62  % (8556)------------------------------
% 1.81/0.62  % (8530)Success in time 0.254 s
%------------------------------------------------------------------------------
