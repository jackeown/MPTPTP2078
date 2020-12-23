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
% DateTime   : Thu Dec  3 13:03:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  308 ( 709 expanded)
%              Number of leaves         :   63 ( 302 expanded)
%              Depth                    :   16
%              Number of atoms          : 1409 (3331 expanded)
%              Number of equality atoms :  271 ( 845 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f163,f173,f179,f234,f257,f269,f293,f346,f403,f412,f436,f484,f493,f516,f583,f673,f693,f727,f745,f772,f812,f845,f853,f902,f928,f1135,f1286,f1287,f1288,f1291])).

fof(f1291,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1288,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1287,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK0 != k1_relat_1(sK2)
    | sK0 != k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1286,plain,
    ( spl4_54
    | ~ spl4_61 ),
    inference(avatar_contradiction_clause,[],[f1285])).

fof(f1285,plain,
    ( $false
    | spl4_54
    | ~ spl4_61 ),
    inference(subsumption_resolution,[],[f1284,f744])).

fof(f744,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_54 ),
    inference(avatar_component_clause,[],[f742])).

fof(f742,plain,
    ( spl4_54
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1284,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f1273,f90])).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1273,plain,
    ( k2_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ spl4_61 ),
    inference(superposition,[],[f90,f807])).

fof(f807,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f805])).

fof(f805,plain,
    ( spl4_61
  <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f1135,plain,
    ( spl4_100
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f1134,f738,f1130])).

fof(f1130,plain,
    ( spl4_100
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f738,plain,
    ( spl4_53
  <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1134,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f1120,f90])).

fof(f1120,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ spl4_53 ),
    inference(superposition,[],[f90,f739])).

fof(f739,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f738])).

fof(f928,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | spl4_65 ),
    inference(avatar_contradiction_clause,[],[f927])).

fof(f927,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | spl4_65 ),
    inference(subsumption_resolution,[],[f926,f172])).

fof(f172,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f926,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_32
    | spl4_65 ),
    inference(subsumption_resolution,[],[f925,f141])).

fof(f141,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f925,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_32
    | spl4_65 ),
    inference(subsumption_resolution,[],[f922,f390])).

fof(f390,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl4_32
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f922,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_65 ),
    inference(resolution,[],[f832,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f832,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_65 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl4_65
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f902,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | spl4_64 ),
    inference(avatar_contradiction_clause,[],[f901])).

fof(f901,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | spl4_64 ),
    inference(subsumption_resolution,[],[f900,f172])).

fof(f900,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_9
    | spl4_64 ),
    inference(subsumption_resolution,[],[f897,f141])).

fof(f897,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_64 ),
    inference(resolution,[],[f828,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f828,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_64 ),
    inference(avatar_component_clause,[],[f826])).

fof(f826,plain,
    ( spl4_64
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f853,plain,
    ( ~ spl4_9
    | ~ spl4_14
    | spl4_57 ),
    inference(avatar_contradiction_clause,[],[f852])).

fof(f852,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_14
    | spl4_57 ),
    inference(subsumption_resolution,[],[f851,f172])).

fof(f851,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_9
    | spl4_57 ),
    inference(subsumption_resolution,[],[f848,f141])).

fof(f848,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_57 ),
    inference(resolution,[],[f777,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f777,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_57 ),
    inference(avatar_component_clause,[],[f775])).

fof(f775,plain,
    ( spl4_57
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f845,plain,
    ( ~ spl4_64
    | ~ spl4_57
    | ~ spl4_65
    | ~ spl4_66
    | spl4_67
    | ~ spl4_68
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f824,f409,f170,f139,f842,f838,f834,f830,f775,f826])).

fof(f834,plain,
    ( spl4_66
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f838,plain,
    ( spl4_67
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f842,plain,
    ( spl4_68
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f409,plain,
    ( spl4_35
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f824,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f823,f172])).

fof(f823,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f792,f141])).

fof(f792,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_35 ),
    inference(superposition,[],[f66,f411])).

fof(f411,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f409])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
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
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f812,plain,
    ( spl4_61
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f811,f409,f388,f170,f139,f805])).

fof(f811,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f810,f172])).

fof(f810,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f809,f141])).

fof(f809,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_32
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f789,f390])).

fof(f789,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f67,f411])).

fof(f67,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f772,plain,
    ( spl4_53
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f771,f400,f388,f170,f139,f738])).

fof(f400,plain,
    ( spl4_34
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f771,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f770,f172])).

fof(f770,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f769,f141])).

fof(f769,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_32
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f753,f390])).

fof(f753,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_34 ),
    inference(superposition,[],[f68,f402])).

fof(f402,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f400])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f745,plain,
    ( ~ spl4_32
    | spl4_52
    | ~ spl4_53
    | ~ spl4_54
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_42
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f732,f578,f490,f176,f170,f154,f139,f742,f738,f734,f388])).

fof(f734,plain,
    ( spl4_52
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f154,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f176,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f490,plain,
    ( spl4_42
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f578,plain,
    ( spl4_47
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f732,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_42
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f731,f580])).

fof(f580,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f578])).

fof(f731,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f730,f172])).

fof(f730,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f729,f141])).

fof(f729,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f728,f178])).

fof(f178,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f728,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f679,f156])).

fof(f156,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f679,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_42 ),
    inference(superposition,[],[f66,f492])).

fof(f492,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f490])).

fof(f727,plain,
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
    inference(avatar_split_clause,[],[f726,f481,f154,f149,f144,f139,f134,f129,f124,f109,f388])).

fof(f109,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f124,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f129,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f134,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f144,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f149,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f481,plain,
    ( spl4_40
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f726,plain,
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
    inference(subsumption_resolution,[],[f725,f141])).

fof(f725,plain,
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
    inference(subsumption_resolution,[],[f724,f136])).

fof(f136,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f724,plain,
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
    inference(subsumption_resolution,[],[f723,f131])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f723,plain,
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
    inference(subsumption_resolution,[],[f712,f111])).

fof(f111,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f712,plain,
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
    inference(subsumption_resolution,[],[f704,f80])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f704,plain,
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
    inference(superposition,[],[f363,f483])).

fof(f483,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f481])).

fof(f363,plain,
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
    inference(subsumption_resolution,[],[f362,f156])).

fof(f362,plain,
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
    inference(subsumption_resolution,[],[f361,f151])).

fof(f151,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f361,plain,
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
    inference(subsumption_resolution,[],[f360,f146])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f360,plain,
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
    inference(trivial_inequality_removal,[],[f359])).

fof(f359,plain,
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
    inference(superposition,[],[f77,f126])).

fof(f126,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f693,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_39 ),
    inference(subsumption_resolution,[],[f691,f156])).

fof(f691,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_39 ),
    inference(subsumption_resolution,[],[f690,f146])).

fof(f690,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_39 ),
    inference(subsumption_resolution,[],[f689,f141])).

fof(f689,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_39 ),
    inference(subsumption_resolution,[],[f686,f131])).

fof(f686,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_39 ),
    inference(resolution,[],[f479,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f479,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl4_39
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f673,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_41 ),
    inference(unit_resulting_resolution,[],[f156,f141,f146,f131,f488,f241])).

fof(f241,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f87,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f488,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl4_41
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f583,plain,
    ( spl4_47
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f582,f429,f578])).

fof(f429,plain,
    ( spl4_37
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f582,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f571,f90])).

fof(f571,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_37 ),
    inference(superposition,[],[f90,f431])).

fof(f431,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f429])).

fof(f516,plain,
    ( spl4_43
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f515,f286,f511])).

fof(f511,plain,
    ( spl4_43
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f286,plain,
    ( spl4_23
  <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f515,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f504,f90])).

fof(f504,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_23 ),
    inference(superposition,[],[f90,f288])).

fof(f288,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f286])).

fof(f493,plain,
    ( ~ spl4_41
    | spl4_42
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f474,f231,f490,f486])).

fof(f231,plain,
    ( spl4_19
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f474,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_19 ),
    inference(resolution,[],[f214,f233])).

fof(f233,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f214,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f81,f164])).

fof(f164,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f84,f85])).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f484,plain,
    ( ~ spl4_39
    | spl4_40
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f473,f160,f481,f477])).

fof(f160,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f473,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f214,f162])).

fof(f162,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f436,plain,
    ( spl4_37
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f435,f266,f176,f154,f114,f429])).

fof(f114,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f266,plain,
    ( spl4_21
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f435,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f434,f178])).

fof(f434,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f433,f156])).

fof(f433,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f415,f116])).

fof(f116,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f415,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_21 ),
    inference(superposition,[],[f68,f268])).

fof(f268,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f266])).

fof(f412,plain,
    ( spl4_35
    | ~ spl4_32
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f407,f343,f139,f134,f129,f109,f388,f409])).

fof(f343,plain,
    ( spl4_30
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f407,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f406,f141])).

fof(f406,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f405,f136])).

fof(f405,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f404,f131])).

fof(f404,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f377,f111])).

fof(f377,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_30 ),
    inference(superposition,[],[f243,f345])).

fof(f345,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f343])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f64,f85])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f403,plain,
    ( spl4_34
    | ~ spl4_32
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f398,f343,f139,f134,f129,f109,f388,f400])).

fof(f398,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f397,f141])).

fof(f397,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f396,f136])).

fof(f396,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f395,f131])).

fof(f395,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f378,f111])).

fof(f378,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_30 ),
    inference(superposition,[],[f244,f345])).

fof(f244,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f65,f85])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f346,plain,
    ( spl4_30
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f341,f160,f154,f149,f144,f139,f134,f129,f343])).

fof(f341,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f340,f141])).

fof(f340,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f339,f136])).

fof(f339,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f338,f131])).

fof(f338,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f337,f156])).

fof(f337,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f336,f151])).

fof(f336,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f333,f146])).

fof(f333,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f331,f162])).

fof(f331,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f83,f85])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f293,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f292,f254,f176,f154,f114,f286])).

fof(f254,plain,
    ( spl4_20
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f292,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f291,f178])).

fof(f291,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f290,f156])).

fof(f290,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f272,f116])).

fof(f272,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(superposition,[],[f67,f256])).

fof(f256,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f254])).

fof(f269,plain,
    ( spl4_21
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f264,f154,f149,f144,f124,f114,f104,f266])).

fof(f104,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f264,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f263,f156])).

fof(f263,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f262,f151])).

fof(f262,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f261,f146])).

fof(f261,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f260,f116])).

fof(f260,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f259,f106])).

fof(f106,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f259,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f244,f126])).

fof(f257,plain,
    ( spl4_20
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f252,f154,f149,f144,f124,f114,f104,f254])).

fof(f252,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f251,f156])).

fof(f251,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f250,f151])).

fof(f250,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f249,f146])).

fof(f249,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f248,f116])).

fof(f248,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f247,f106])).

fof(f247,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f246])).

fof(f246,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f243,f126])).

fof(f234,plain,
    ( spl4_19
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f229,f160,f154,f144,f139,f129,f231])).

fof(f229,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f228,f156])).

fof(f228,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f227,f146])).

fof(f227,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f226,f141])).

fof(f226,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f223,f131])).

fof(f223,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f162,f88])).

fof(f179,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f174,f144,f176])).

fof(f174,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f166,f92])).

fof(f92,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f166,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f91,f146])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f173,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f168,f129,f170])).

fof(f168,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f165,f92])).

fof(f165,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f91,f131])).

fof(f163,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f158,f119,f160])).

fof(f119,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f158,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f121,f85])).

fof(f121,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f157,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f52,f154])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f49,f48])).

fof(f48,plain,
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

fof(f49,plain,
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f152,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f53,f149])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f147,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f54,f144])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f142,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f55,f139])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f137,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f56,f134])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f132,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f57,f129])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f127,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f124])).

fof(f58,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f122,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f59,f119])).

fof(f59,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f117,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f61,f109])).

fof(f61,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f62,f104])).

fof(f62,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f99])).

fof(f99,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (18734)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.49  % (18735)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (18754)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (18743)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (18759)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (18733)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (18739)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (18740)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (18741)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (18736)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (18747)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (18745)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (18760)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % (18737)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (18746)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (18738)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (18753)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (18744)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (18748)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (18742)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (18732)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (18756)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (18762)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (18757)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (18752)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (18749)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (18755)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (18751)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (18761)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (18758)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  % (18748)Refutation not found, incomplete strategy% (18748)------------------------------
% 0.20/0.56  % (18748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18748)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18748)Memory used [KB]: 10746
% 0.20/0.56  % (18748)Time elapsed: 0.153 s
% 0.20/0.56  % (18748)------------------------------
% 0.20/0.56  % (18748)------------------------------
% 0.20/0.56  % (18754)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1292,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f163,f173,f179,f234,f257,f269,f293,f346,f403,f412,f436,f484,f493,f516,f583,f673,f693,f727,f745,f772,f812,f845,f853,f902,f928,f1135,f1286,f1287,f1288,f1291])).
% 0.20/0.58  fof(f1291,plain,(
% 0.20/0.58    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | k2_funct_1(sK2) = sK3),
% 0.20/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.58  fof(f1288,plain,(
% 0.20/0.58    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 0.20/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.58  fof(f1287,plain,(
% 0.20/0.58    sK2 != k2_funct_1(sK3) | sK0 != k1_relat_1(sK2) | sK0 != k2_relat_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.20/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.58  fof(f1286,plain,(
% 0.20/0.58    spl4_54 | ~spl4_61),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1285])).
% 0.20/0.58  fof(f1285,plain,(
% 0.20/0.58    $false | (spl4_54 | ~spl4_61)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1284,f744])).
% 0.20/0.58  fof(f744,plain,(
% 0.20/0.58    sK1 != k1_relat_1(sK3) | spl4_54),
% 0.20/0.58    inference(avatar_component_clause,[],[f742])).
% 0.20/0.58  fof(f742,plain,(
% 0.20/0.58    spl4_54 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.20/0.58  fof(f1284,plain,(
% 0.20/0.58    sK1 = k1_relat_1(sK3) | ~spl4_61),
% 0.20/0.58    inference(forward_demodulation,[],[f1273,f90])).
% 0.20/0.58  fof(f90,plain,(
% 0.20/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.58  fof(f1273,plain,(
% 0.20/0.58    k2_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~spl4_61),
% 0.20/0.58    inference(superposition,[],[f90,f807])).
% 0.20/0.58  fof(f807,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~spl4_61),
% 0.20/0.58    inference(avatar_component_clause,[],[f805])).
% 0.20/0.58  fof(f805,plain,(
% 0.20/0.58    spl4_61 <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.20/0.58  fof(f1135,plain,(
% 0.20/0.58    spl4_100 | ~spl4_53),
% 0.20/0.58    inference(avatar_split_clause,[],[f1134,f738,f1130])).
% 0.20/0.58  fof(f1130,plain,(
% 0.20/0.58    spl4_100 <=> sK0 = k2_relat_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).
% 0.20/0.58  fof(f738,plain,(
% 0.20/0.58    spl4_53 <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.20/0.58  fof(f1134,plain,(
% 0.20/0.58    sK0 = k2_relat_1(sK3) | ~spl4_53),
% 0.20/0.58    inference(forward_demodulation,[],[f1120,f90])).
% 0.20/0.58  fof(f1120,plain,(
% 0.20/0.58    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~spl4_53),
% 0.20/0.58    inference(superposition,[],[f90,f739])).
% 0.20/0.58  fof(f739,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~spl4_53),
% 0.20/0.58    inference(avatar_component_clause,[],[f738])).
% 0.20/0.58  fof(f928,plain,(
% 0.20/0.58    ~spl4_9 | ~spl4_14 | ~spl4_32 | spl4_65),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f927])).
% 0.20/0.58  fof(f927,plain,(
% 0.20/0.58    $false | (~spl4_9 | ~spl4_14 | ~spl4_32 | spl4_65)),
% 0.20/0.58    inference(subsumption_resolution,[],[f926,f172])).
% 0.20/0.58  fof(f172,plain,(
% 0.20/0.58    v1_relat_1(sK3) | ~spl4_14),
% 0.20/0.58    inference(avatar_component_clause,[],[f170])).
% 0.20/0.58  fof(f170,plain,(
% 0.20/0.58    spl4_14 <=> v1_relat_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.58  fof(f926,plain,(
% 0.20/0.58    ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_32 | spl4_65)),
% 0.20/0.58    inference(subsumption_resolution,[],[f925,f141])).
% 0.20/0.58  fof(f141,plain,(
% 0.20/0.58    v1_funct_1(sK3) | ~spl4_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f139])).
% 0.20/0.58  fof(f139,plain,(
% 0.20/0.58    spl4_9 <=> v1_funct_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.58  fof(f925,plain,(
% 0.20/0.58    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_32 | spl4_65)),
% 0.20/0.58    inference(subsumption_resolution,[],[f922,f390])).
% 0.20/0.58  fof(f390,plain,(
% 0.20/0.58    v2_funct_1(sK3) | ~spl4_32),
% 0.20/0.58    inference(avatar_component_clause,[],[f388])).
% 0.20/0.58  fof(f388,plain,(
% 0.20/0.58    spl4_32 <=> v2_funct_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.58  fof(f922,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_65),
% 0.20/0.58    inference(resolution,[],[f832,f74])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.58  fof(f832,plain,(
% 0.20/0.58    ~v2_funct_1(k2_funct_1(sK3)) | spl4_65),
% 0.20/0.58    inference(avatar_component_clause,[],[f830])).
% 0.20/0.58  fof(f830,plain,(
% 0.20/0.58    spl4_65 <=> v2_funct_1(k2_funct_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.20/0.58  fof(f902,plain,(
% 0.20/0.58    ~spl4_9 | ~spl4_14 | spl4_64),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f901])).
% 0.20/0.58  fof(f901,plain,(
% 0.20/0.58    $false | (~spl4_9 | ~spl4_14 | spl4_64)),
% 0.20/0.58    inference(subsumption_resolution,[],[f900,f172])).
% 0.20/0.58  fof(f900,plain,(
% 0.20/0.58    ~v1_relat_1(sK3) | (~spl4_9 | spl4_64)),
% 0.20/0.58    inference(subsumption_resolution,[],[f897,f141])).
% 0.20/0.58  fof(f897,plain,(
% 0.20/0.58    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_64),
% 0.20/0.58    inference(resolution,[],[f828,f70])).
% 0.20/0.58  fof(f70,plain,(
% 0.20/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f32])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f6])).
% 0.20/0.58  fof(f6,axiom,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.58  fof(f828,plain,(
% 0.20/0.58    ~v1_relat_1(k2_funct_1(sK3)) | spl4_64),
% 0.20/0.58    inference(avatar_component_clause,[],[f826])).
% 0.20/0.58  fof(f826,plain,(
% 0.20/0.58    spl4_64 <=> v1_relat_1(k2_funct_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.20/0.58  fof(f853,plain,(
% 0.20/0.58    ~spl4_9 | ~spl4_14 | spl4_57),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f852])).
% 0.20/0.58  fof(f852,plain,(
% 0.20/0.58    $false | (~spl4_9 | ~spl4_14 | spl4_57)),
% 0.20/0.58    inference(subsumption_resolution,[],[f851,f172])).
% 0.20/0.58  fof(f851,plain,(
% 0.20/0.58    ~v1_relat_1(sK3) | (~spl4_9 | spl4_57)),
% 0.20/0.58    inference(subsumption_resolution,[],[f848,f141])).
% 0.20/0.58  fof(f848,plain,(
% 0.20/0.58    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_57),
% 0.20/0.58    inference(resolution,[],[f777,f71])).
% 0.20/0.58  fof(f71,plain,(
% 0.20/0.58    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f33])).
% 0.20/0.58  fof(f777,plain,(
% 0.20/0.58    ~v1_funct_1(k2_funct_1(sK3)) | spl4_57),
% 0.20/0.58    inference(avatar_component_clause,[],[f775])).
% 0.20/0.58  fof(f775,plain,(
% 0.20/0.58    spl4_57 <=> v1_funct_1(k2_funct_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.20/0.58  fof(f845,plain,(
% 0.20/0.58    ~spl4_64 | ~spl4_57 | ~spl4_65 | ~spl4_66 | spl4_67 | ~spl4_68 | ~spl4_9 | ~spl4_14 | ~spl4_35),
% 0.20/0.58    inference(avatar_split_clause,[],[f824,f409,f170,f139,f842,f838,f834,f830,f775,f826])).
% 0.20/0.58  fof(f834,plain,(
% 0.20/0.58    spl4_66 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.20/0.58  fof(f838,plain,(
% 0.20/0.58    spl4_67 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.20/0.58  fof(f842,plain,(
% 0.20/0.58    spl4_68 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.20/0.58  fof(f409,plain,(
% 0.20/0.58    spl4_35 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.58  fof(f824,plain,(
% 0.20/0.58    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_35)),
% 0.20/0.58    inference(subsumption_resolution,[],[f823,f172])).
% 0.20/0.58  fof(f823,plain,(
% 0.20/0.58    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_35)),
% 0.20/0.58    inference(subsumption_resolution,[],[f792,f141])).
% 0.20/0.58  fof(f792,plain,(
% 0.20/0.58    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_35),
% 0.20/0.58    inference(superposition,[],[f66,f411])).
% 0.20/0.58  fof(f411,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_35),
% 0.20/0.58    inference(avatar_component_clause,[],[f409])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.20/0.58  fof(f812,plain,(
% 0.20/0.58    spl4_61 | ~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_35),
% 0.20/0.58    inference(avatar_split_clause,[],[f811,f409,f388,f170,f139,f805])).
% 0.20/0.58  fof(f811,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_35)),
% 0.20/0.58    inference(subsumption_resolution,[],[f810,f172])).
% 0.20/0.58  fof(f810,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_32 | ~spl4_35)),
% 0.20/0.58    inference(subsumption_resolution,[],[f809,f141])).
% 0.20/0.58  fof(f809,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_32 | ~spl4_35)),
% 0.20/0.58    inference(subsumption_resolution,[],[f789,f390])).
% 0.20/0.58  fof(f789,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_35),
% 0.20/0.58    inference(superposition,[],[f67,f411])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(flattening,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,axiom,(
% 0.20/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.58  fof(f772,plain,(
% 0.20/0.58    spl4_53 | ~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_34),
% 0.20/0.58    inference(avatar_split_clause,[],[f771,f400,f388,f170,f139,f738])).
% 0.20/0.58  fof(f400,plain,(
% 0.20/0.58    spl4_34 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.58  fof(f771,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_32 | ~spl4_34)),
% 0.20/0.58    inference(subsumption_resolution,[],[f770,f172])).
% 0.20/0.58  fof(f770,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_32 | ~spl4_34)),
% 0.20/0.58    inference(subsumption_resolution,[],[f769,f141])).
% 0.20/0.58  fof(f769,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_32 | ~spl4_34)),
% 0.20/0.58    inference(subsumption_resolution,[],[f753,f390])).
% 0.20/0.58  fof(f753,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_34),
% 0.20/0.58    inference(superposition,[],[f68,f402])).
% 0.20/0.58  fof(f402,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_34),
% 0.20/0.58    inference(avatar_component_clause,[],[f400])).
% 0.20/0.58  fof(f68,plain,(
% 0.20/0.58    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f745,plain,(
% 0.20/0.58    ~spl4_32 | spl4_52 | ~spl4_53 | ~spl4_54 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_42 | ~spl4_47),
% 0.20/0.58    inference(avatar_split_clause,[],[f732,f578,f490,f176,f170,f154,f139,f742,f738,f734,f388])).
% 0.20/0.58  fof(f734,plain,(
% 0.20/0.58    spl4_52 <=> sK2 = k2_funct_1(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.20/0.58  fof(f154,plain,(
% 0.20/0.58    spl4_12 <=> v1_funct_1(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.58  fof(f176,plain,(
% 0.20/0.58    spl4_15 <=> v1_relat_1(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.58  fof(f490,plain,(
% 0.20/0.58    spl4_42 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.58  fof(f578,plain,(
% 0.20/0.58    spl4_47 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.20/0.58  fof(f732,plain,(
% 0.20/0.58    sK1 != k1_relat_1(sK3) | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_42 | ~spl4_47)),
% 0.20/0.58    inference(forward_demodulation,[],[f731,f580])).
% 0.20/0.58  fof(f580,plain,(
% 0.20/0.58    sK1 = k2_relat_1(sK2) | ~spl4_47),
% 0.20/0.58    inference(avatar_component_clause,[],[f578])).
% 0.20/0.58  fof(f731,plain,(
% 0.20/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_42)),
% 0.20/0.58    inference(subsumption_resolution,[],[f730,f172])).
% 0.20/0.58  fof(f730,plain,(
% 0.20/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_42)),
% 0.20/0.58    inference(subsumption_resolution,[],[f729,f141])).
% 0.20/0.58  fof(f729,plain,(
% 0.20/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_42)),
% 0.20/0.58    inference(subsumption_resolution,[],[f728,f178])).
% 0.20/0.58  fof(f178,plain,(
% 0.20/0.58    v1_relat_1(sK2) | ~spl4_15),
% 0.20/0.58    inference(avatar_component_clause,[],[f176])).
% 0.20/0.58  fof(f728,plain,(
% 0.20/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_42)),
% 0.20/0.58    inference(subsumption_resolution,[],[f679,f156])).
% 0.20/0.58  fof(f156,plain,(
% 0.20/0.58    v1_funct_1(sK2) | ~spl4_12),
% 0.20/0.58    inference(avatar_component_clause,[],[f154])).
% 0.20/0.58  fof(f679,plain,(
% 0.20/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_42),
% 0.20/0.58    inference(superposition,[],[f66,f492])).
% 0.20/0.58  fof(f492,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_42),
% 0.20/0.58    inference(avatar_component_clause,[],[f490])).
% 0.20/0.58  fof(f727,plain,(
% 0.20/0.58    spl4_32 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40),
% 0.20/0.58    inference(avatar_split_clause,[],[f726,f481,f154,f149,f144,f139,f134,f129,f124,f109,f388])).
% 0.20/0.58  fof(f109,plain,(
% 0.20/0.58    spl4_3 <=> k1_xboole_0 = sK0),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.58  fof(f124,plain,(
% 0.20/0.58    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.58  fof(f129,plain,(
% 0.20/0.58    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.58  fof(f134,plain,(
% 0.20/0.58    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.58  fof(f144,plain,(
% 0.20/0.58    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.58  fof(f149,plain,(
% 0.20/0.58    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.58  fof(f481,plain,(
% 0.20/0.58    spl4_40 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.58  fof(f726,plain,(
% 0.20/0.58    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f725,f141])).
% 0.20/0.58  fof(f725,plain,(
% 0.20/0.58    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f724,f136])).
% 0.20/0.58  fof(f136,plain,(
% 0.20/0.58    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 0.20/0.58    inference(avatar_component_clause,[],[f134])).
% 0.20/0.58  fof(f724,plain,(
% 0.20/0.58    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f723,f131])).
% 0.20/0.58  fof(f131,plain,(
% 0.20/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 0.20/0.58    inference(avatar_component_clause,[],[f129])).
% 0.20/0.58  fof(f723,plain,(
% 0.20/0.58    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f712,f111])).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    k1_xboole_0 != sK0 | spl4_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f109])).
% 0.20/0.58  fof(f712,plain,(
% 0.20/0.58    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f704,f80])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.58  fof(f704,plain,(
% 0.20/0.58    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_40)),
% 0.20/0.58    inference(superposition,[],[f363,f483])).
% 0.20/0.58  fof(f483,plain,(
% 0.20/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_40),
% 0.20/0.58    inference(avatar_component_clause,[],[f481])).
% 0.20/0.58  fof(f363,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f362,f156])).
% 0.20/0.58  fof(f362,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 0.20/0.58    inference(subsumption_resolution,[],[f361,f151])).
% 0.20/0.58  fof(f151,plain,(
% 0.20/0.58    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 0.20/0.58    inference(avatar_component_clause,[],[f149])).
% 0.20/0.58  fof(f361,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 0.20/0.58    inference(subsumption_resolution,[],[f360,f146])).
% 0.20/0.58  fof(f146,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 0.20/0.58    inference(avatar_component_clause,[],[f144])).
% 0.20/0.58  fof(f360,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f359])).
% 0.20/0.58  fof(f359,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 0.20/0.58    inference(superposition,[],[f77,f126])).
% 0.20/0.58  fof(f126,plain,(
% 0.20/0.58    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f124])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.58    inference(flattening,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.58    inference(ennf_transformation,[],[f17])).
% 0.20/0.58  fof(f17,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 0.20/0.58  fof(f693,plain,(
% 0.20/0.58    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f692])).
% 0.20/0.58  fof(f692,plain,(
% 0.20/0.58    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_39)),
% 0.20/0.58    inference(subsumption_resolution,[],[f691,f156])).
% 0.20/0.58  fof(f691,plain,(
% 0.20/0.58    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_39)),
% 0.20/0.58    inference(subsumption_resolution,[],[f690,f146])).
% 0.20/0.58  fof(f690,plain,(
% 0.20/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_39)),
% 0.20/0.58    inference(subsumption_resolution,[],[f689,f141])).
% 0.20/0.58  fof(f689,plain,(
% 0.20/0.58    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_39)),
% 0.20/0.58    inference(subsumption_resolution,[],[f686,f131])).
% 0.20/0.58  fof(f686,plain,(
% 0.20/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_39),
% 0.20/0.58    inference(resolution,[],[f479,f87])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.58    inference(flattening,[],[f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.58    inference(ennf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.58  fof(f479,plain,(
% 0.20/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_39),
% 0.20/0.58    inference(avatar_component_clause,[],[f477])).
% 0.20/0.58  fof(f477,plain,(
% 0.20/0.58    spl4_39 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.58  fof(f673,plain,(
% 0.20/0.58    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_41),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f671])).
% 0.20/0.58  fof(f671,plain,(
% 0.20/0.58    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_41)),
% 0.20/0.58    inference(unit_resulting_resolution,[],[f156,f141,f146,f131,f488,f241])).
% 0.20/0.58  fof(f241,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f240])).
% 0.20/0.58  fof(f240,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.58    inference(superposition,[],[f87,f88])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.58    inference(flattening,[],[f44])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.58  fof(f488,plain,(
% 0.20/0.58    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_41),
% 0.20/0.58    inference(avatar_component_clause,[],[f486])).
% 0.20/0.58  fof(f486,plain,(
% 0.20/0.58    spl4_41 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.20/0.58  fof(f583,plain,(
% 0.20/0.58    spl4_47 | ~spl4_37),
% 0.20/0.58    inference(avatar_split_clause,[],[f582,f429,f578])).
% 0.20/0.58  fof(f429,plain,(
% 0.20/0.58    spl4_37 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.58  fof(f582,plain,(
% 0.20/0.58    sK1 = k2_relat_1(sK2) | ~spl4_37),
% 0.20/0.58    inference(forward_demodulation,[],[f571,f90])).
% 0.20/0.58  fof(f571,plain,(
% 0.20/0.58    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1)) | ~spl4_37),
% 0.20/0.58    inference(superposition,[],[f90,f431])).
% 0.20/0.58  fof(f431,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~spl4_37),
% 0.20/0.58    inference(avatar_component_clause,[],[f429])).
% 0.20/0.58  fof(f516,plain,(
% 0.20/0.58    spl4_43 | ~spl4_23),
% 0.20/0.58    inference(avatar_split_clause,[],[f515,f286,f511])).
% 0.20/0.58  fof(f511,plain,(
% 0.20/0.58    spl4_43 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.20/0.58  fof(f286,plain,(
% 0.20/0.58    spl4_23 <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.58  fof(f515,plain,(
% 0.20/0.58    sK0 = k1_relat_1(sK2) | ~spl4_23),
% 0.20/0.58    inference(forward_demodulation,[],[f504,f90])).
% 0.20/0.58  fof(f504,plain,(
% 0.20/0.58    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~spl4_23),
% 0.20/0.58    inference(superposition,[],[f90,f288])).
% 0.20/0.58  fof(f288,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~spl4_23),
% 0.20/0.58    inference(avatar_component_clause,[],[f286])).
% 0.20/0.58  fof(f493,plain,(
% 0.20/0.58    ~spl4_41 | spl4_42 | ~spl4_19),
% 0.20/0.58    inference(avatar_split_clause,[],[f474,f231,f490,f486])).
% 0.20/0.58  fof(f231,plain,(
% 0.20/0.58    spl4_19 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.58  fof(f474,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_19),
% 0.20/0.58    inference(resolution,[],[f214,f233])).
% 0.20/0.58  fof(f233,plain,(
% 0.20/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_19),
% 0.20/0.58    inference(avatar_component_clause,[],[f231])).
% 0.20/0.58  fof(f214,plain,(
% 0.20/0.58    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.20/0.58    inference(resolution,[],[f81,f164])).
% 0.20/0.58  fof(f164,plain,(
% 0.20/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f84,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.58    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f51])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(nnf_transformation,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(flattening,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.58    inference(ennf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.58  fof(f484,plain,(
% 0.20/0.58    ~spl4_39 | spl4_40 | ~spl4_13),
% 0.20/0.58    inference(avatar_split_clause,[],[f473,f160,f481,f477])).
% 0.20/0.58  fof(f160,plain,(
% 0.20/0.58    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.58  fof(f473,plain,(
% 0.20/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 0.20/0.58    inference(resolution,[],[f214,f162])).
% 0.20/0.58  fof(f162,plain,(
% 0.20/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 0.20/0.58    inference(avatar_component_clause,[],[f160])).
% 0.20/0.58  fof(f436,plain,(
% 0.20/0.58    spl4_37 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21),
% 0.20/0.58    inference(avatar_split_clause,[],[f435,f266,f176,f154,f114,f429])).
% 0.20/0.58  fof(f114,plain,(
% 0.20/0.58    spl4_4 <=> v2_funct_1(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.58  fof(f266,plain,(
% 0.20/0.58    spl4_21 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.58  fof(f435,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21)),
% 0.20/0.58    inference(subsumption_resolution,[],[f434,f178])).
% 0.20/0.58  fof(f434,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_21)),
% 0.20/0.58    inference(subsumption_resolution,[],[f433,f156])).
% 0.20/0.58  fof(f433,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_21)),
% 0.20/0.58    inference(subsumption_resolution,[],[f415,f116])).
% 0.20/0.58  fof(f116,plain,(
% 0.20/0.58    v2_funct_1(sK2) | ~spl4_4),
% 0.20/0.58    inference(avatar_component_clause,[],[f114])).
% 0.20/0.58  fof(f415,plain,(
% 0.20/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_21),
% 0.20/0.58    inference(superposition,[],[f68,f268])).
% 0.20/0.58  fof(f268,plain,(
% 0.20/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_21),
% 0.20/0.58    inference(avatar_component_clause,[],[f266])).
% 0.20/0.58  fof(f412,plain,(
% 0.20/0.58    spl4_35 | ~spl4_32 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_30),
% 0.20/0.58    inference(avatar_split_clause,[],[f407,f343,f139,f134,f129,f109,f388,f409])).
% 0.20/0.58  fof(f343,plain,(
% 0.20/0.58    spl4_30 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.58  fof(f407,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f406,f141])).
% 0.20/0.58  fof(f406,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f405,f136])).
% 0.20/0.58  fof(f405,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f404,f131])).
% 0.20/0.58  fof(f404,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f377,f111])).
% 0.20/0.58  fof(f377,plain,(
% 0.20/0.58    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_30),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f376])).
% 0.20/0.58  fof(f376,plain,(
% 0.20/0.58    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_30),
% 0.20/0.58    inference(superposition,[],[f243,f345])).
% 0.20/0.58  fof(f345,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_30),
% 0.20/0.58    inference(avatar_component_clause,[],[f343])).
% 0.20/0.58  fof(f243,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f64,f85])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f25])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(flattening,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f18])).
% 0.20/0.58  fof(f18,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.58  fof(f403,plain,(
% 0.20/0.58    spl4_34 | ~spl4_32 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_30),
% 0.20/0.58    inference(avatar_split_clause,[],[f398,f343,f139,f134,f129,f109,f388,f400])).
% 0.20/0.58  fof(f398,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f397,f141])).
% 0.20/0.58  fof(f397,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f396,f136])).
% 0.20/0.58  fof(f396,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f395,f131])).
% 0.20/0.58  fof(f395,plain,(
% 0.20/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_30)),
% 0.20/0.58    inference(subsumption_resolution,[],[f378,f111])).
% 0.20/0.58  fof(f378,plain,(
% 0.20/0.58    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_30),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f375])).
% 0.20/0.58  fof(f375,plain,(
% 0.20/0.58    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_30),
% 0.20/0.58    inference(superposition,[],[f244,f345])).
% 0.20/0.58  fof(f244,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f65,f85])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f25])).
% 0.20/0.58  fof(f346,plain,(
% 0.20/0.58    spl4_30 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 0.20/0.58    inference(avatar_split_clause,[],[f341,f160,f154,f149,f144,f139,f134,f129,f343])).
% 0.20/0.58  fof(f341,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f340,f141])).
% 0.20/0.58  fof(f340,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f339,f136])).
% 0.20/0.58  fof(f339,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f338,f131])).
% 0.20/0.58  fof(f338,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f337,f156])).
% 0.20/0.58  fof(f337,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f336,f151])).
% 0.20/0.58  fof(f336,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f333,f146])).
% 0.20/0.58  fof(f333,plain,(
% 0.20/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 0.20/0.58    inference(resolution,[],[f331,f162])).
% 0.20/0.58  fof(f331,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(forward_demodulation,[],[f83,f85])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(flattening,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 0.20/0.58  fof(f293,plain,(
% 0.20/0.58    spl4_23 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_20),
% 0.20/0.58    inference(avatar_split_clause,[],[f292,f254,f176,f154,f114,f286])).
% 0.20/0.58  fof(f254,plain,(
% 0.20/0.58    spl4_20 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.58  fof(f292,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_20)),
% 0.20/0.58    inference(subsumption_resolution,[],[f291,f178])).
% 0.20/0.58  fof(f291,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_20)),
% 0.20/0.58    inference(subsumption_resolution,[],[f290,f156])).
% 0.20/0.58  fof(f290,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_20)),
% 0.20/0.58    inference(subsumption_resolution,[],[f272,f116])).
% 0.20/0.58  fof(f272,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_20),
% 0.20/0.58    inference(superposition,[],[f67,f256])).
% 0.20/0.58  fof(f256,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_20),
% 0.20/0.58    inference(avatar_component_clause,[],[f254])).
% 0.20/0.58  fof(f269,plain,(
% 0.20/0.58    spl4_21 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 0.20/0.58    inference(avatar_split_clause,[],[f264,f154,f149,f144,f124,f114,f104,f266])).
% 0.20/0.58  fof(f104,plain,(
% 0.20/0.58    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.58  fof(f264,plain,(
% 0.20/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f263,f156])).
% 0.20/0.58  fof(f263,plain,(
% 0.20/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 0.20/0.58    inference(subsumption_resolution,[],[f262,f151])).
% 0.20/0.58  fof(f262,plain,(
% 0.20/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 0.20/0.58    inference(subsumption_resolution,[],[f261,f146])).
% 0.20/0.58  fof(f261,plain,(
% 0.20/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f260,f116])).
% 0.20/0.58  fof(f260,plain,(
% 0.20/0.58    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f259,f106])).
% 0.20/0.58  fof(f106,plain,(
% 0.20/0.58    k1_xboole_0 != sK1 | spl4_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f104])).
% 0.20/0.58  fof(f259,plain,(
% 0.20/0.58    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f258])).
% 0.20/0.58  fof(f258,plain,(
% 0.20/0.58    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.20/0.58    inference(superposition,[],[f244,f126])).
% 0.20/0.58  fof(f257,plain,(
% 0.20/0.58    spl4_20 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 0.20/0.58    inference(avatar_split_clause,[],[f252,f154,f149,f144,f124,f114,f104,f254])).
% 0.20/0.58  fof(f252,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.58    inference(subsumption_resolution,[],[f251,f156])).
% 0.20/0.58  fof(f251,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 0.20/0.58    inference(subsumption_resolution,[],[f250,f151])).
% 0.20/0.58  fof(f250,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 0.20/0.58    inference(subsumption_resolution,[],[f249,f146])).
% 0.20/0.58  fof(f249,plain,(
% 0.20/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f248,f116])).
% 0.20/0.58  fof(f248,plain,(
% 0.20/0.58    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 0.20/0.58    inference(subsumption_resolution,[],[f247,f106])).
% 0.20/0.58  fof(f247,plain,(
% 0.20/0.58    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f246])).
% 0.20/0.58  fof(f246,plain,(
% 0.20/0.58    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.20/0.58    inference(superposition,[],[f243,f126])).
% 0.20/0.58  fof(f234,plain,(
% 0.20/0.58    spl4_19 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 0.20/0.58    inference(avatar_split_clause,[],[f229,f160,f154,f144,f139,f129,f231])).
% 0.20/0.58  fof(f229,plain,(
% 0.20/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f228,f156])).
% 0.20/0.58  fof(f228,plain,(
% 0.20/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f227,f146])).
% 0.20/0.58  fof(f227,plain,(
% 0.20/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f226,f141])).
% 0.20/0.58  fof(f226,plain,(
% 0.20/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 0.20/0.58    inference(subsumption_resolution,[],[f223,f131])).
% 0.20/0.58  fof(f223,plain,(
% 0.20/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 0.20/0.58    inference(superposition,[],[f162,f88])).
% 0.20/0.58  fof(f179,plain,(
% 0.20/0.58    spl4_15 | ~spl4_10),
% 0.20/0.58    inference(avatar_split_clause,[],[f174,f144,f176])).
% 0.20/0.58  fof(f174,plain,(
% 0.20/0.58    v1_relat_1(sK2) | ~spl4_10),
% 0.20/0.58    inference(subsumption_resolution,[],[f166,f92])).
% 0.20/0.58  fof(f92,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.58  fof(f166,plain,(
% 0.20/0.58    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 0.20/0.58    inference(resolution,[],[f91,f146])).
% 0.20/0.58  fof(f91,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.59  fof(f173,plain,(
% 0.20/0.59    spl4_14 | ~spl4_7),
% 0.20/0.59    inference(avatar_split_clause,[],[f168,f129,f170])).
% 0.20/0.59  fof(f168,plain,(
% 0.20/0.59    v1_relat_1(sK3) | ~spl4_7),
% 0.20/0.59    inference(subsumption_resolution,[],[f165,f92])).
% 0.20/0.59  fof(f165,plain,(
% 0.20/0.59    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 0.20/0.59    inference(resolution,[],[f91,f131])).
% 0.20/0.59  fof(f163,plain,(
% 0.20/0.59    spl4_13 | ~spl4_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f158,f119,f160])).
% 0.20/0.59  fof(f119,plain,(
% 0.20/0.59    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.59  fof(f158,plain,(
% 0.20/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 0.20/0.59    inference(backward_demodulation,[],[f121,f85])).
% 0.20/0.59  fof(f121,plain,(
% 0.20/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f119])).
% 0.20/0.59  fof(f157,plain,(
% 0.20/0.59    spl4_12),
% 0.20/0.59    inference(avatar_split_clause,[],[f52,f154])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    v1_funct_1(sK2)),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f50,plain,(
% 0.20/0.59    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f49,f48])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.59    inference(flattening,[],[f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.59    inference(ennf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.59    inference(negated_conjecture,[],[f19])).
% 0.20/0.59  fof(f19,conjecture,(
% 0.20/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.20/0.59  fof(f152,plain,(
% 0.20/0.59    spl4_11),
% 0.20/0.59    inference(avatar_split_clause,[],[f53,f149])).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f147,plain,(
% 0.20/0.59    spl4_10),
% 0.20/0.59    inference(avatar_split_clause,[],[f54,f144])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f142,plain,(
% 0.20/0.59    spl4_9),
% 0.20/0.59    inference(avatar_split_clause,[],[f55,f139])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    v1_funct_1(sK3)),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f137,plain,(
% 0.20/0.59    spl4_8),
% 0.20/0.59    inference(avatar_split_clause,[],[f56,f134])).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f132,plain,(
% 0.20/0.59    spl4_7),
% 0.20/0.59    inference(avatar_split_clause,[],[f57,f129])).
% 0.20/0.59  fof(f57,plain,(
% 0.20/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f127,plain,(
% 0.20/0.59    spl4_6),
% 0.20/0.59    inference(avatar_split_clause,[],[f58,f124])).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f122,plain,(
% 0.20/0.59    spl4_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f59,f119])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    spl4_4),
% 0.20/0.59    inference(avatar_split_clause,[],[f60,f114])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    v2_funct_1(sK2)),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f112,plain,(
% 0.20/0.59    ~spl4_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f61,f109])).
% 0.20/0.59  fof(f61,plain,(
% 0.20/0.59    k1_xboole_0 != sK0),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f107,plain,(
% 0.20/0.59    ~spl4_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f62,f104])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    k1_xboole_0 != sK1),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    ~spl4_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f63,f99])).
% 0.20/0.59  fof(f99,plain,(
% 0.20/0.59    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.59  fof(f63,plain,(
% 0.20/0.59    k2_funct_1(sK2) != sK3),
% 0.20/0.59    inference(cnf_transformation,[],[f50])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (18754)------------------------------
% 0.20/0.59  % (18754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (18754)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (18754)Memory used [KB]: 7419
% 0.20/0.59  % (18754)Time elapsed: 0.161 s
% 0.20/0.59  % (18754)------------------------------
% 0.20/0.59  % (18754)------------------------------
% 0.20/0.59  % (18727)Success in time 0.231 s
%------------------------------------------------------------------------------
