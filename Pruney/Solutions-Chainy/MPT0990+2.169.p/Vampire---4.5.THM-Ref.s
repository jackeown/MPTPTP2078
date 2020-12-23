%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:58 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 352 expanded)
%              Number of leaves         :   41 ( 135 expanded)
%              Depth                    :   23
%              Number of atoms          :  787 (2122 expanded)
%              Number of equality atoms :  196 ( 640 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f714,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f157,f167,f173,f197,f221,f228,f238,f258,f278,f323,f340,f713])).

fof(f713,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(trivial_inequality_removal,[],[f711])).

fof(f711,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f710,f194])).

fof(f194,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f710,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(sK1)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f709,f235])).

fof(f235,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f709,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(trivial_inequality_removal,[],[f708])).

fof(f708,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f707,f255])).

fof(f255,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_24
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f707,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f706,f110])).

fof(f110,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f706,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f705,f172])).

fof(f172,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f705,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f704,f150])).

fof(f150,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f704,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f703,f166])).

fof(f166,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f703,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f702,f135])).

fof(f135,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f702,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | spl4_1
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f697,f95])).

fof(f95,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f697,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_29 ),
    inference(superposition,[],[f384,f322])).

fof(f322,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl4_29
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f384,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1))
      | k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f289,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k2_funct_1(X0),X1)
      | k2_funct_1(X0) = X2
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f288,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X2
      | k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k2_funct_1(X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f281,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X2
      | k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k2_funct_1(X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f90,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f90,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).

fof(f340,plain,
    ( ~ spl4_7
    | ~ spl4_10
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_10
    | spl4_28 ),
    inference(unit_resulting_resolution,[],[f140,f125,f318,f266])).

fof(f266,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f79,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f318,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl4_28
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f125,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f323,plain,
    ( ~ spl4_28
    | spl4_29
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f304,f275,f320,f316])).

fof(f275,plain,
    ( spl4_25
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f304,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_25 ),
    inference(resolution,[],[f246,f277])).

fof(f277,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f275])).

fof(f246,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f72,f158])).

fof(f158,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f74,f75])).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f278,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f273,f154,f148,f138,f133,f123,f275])).

fof(f154,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f273,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f272,f150])).

fof(f272,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f271,f140])).

fof(f271,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f270,f135])).

fof(f270,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f269,f125])).

fof(f269,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f156,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
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
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f156,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f258,plain,
    ( spl4_24
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f257,f225,f138,f253])).

fof(f225,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f257,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f249,f140])).

fof(f249,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_22 ),
    inference(superposition,[],[f81,f227])).

fof(f227,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f225])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f238,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f237,f218,f123,f233])).

fof(f218,plain,
    ( spl4_21
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f237,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f230,f125])).

fof(f230,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_21 ),
    inference(superposition,[],[f81,f220])).

fof(f220,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f218])).

fof(f228,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f223,f143,f138,f98,f225])).

fof(f98,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f143,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f223,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f222,f100])).

fof(f100,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f222,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f213,f145])).

fof(f145,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f213,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f66,f140])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f221,plain,
    ( spl4_21
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f216,f128,f123,f103,f218])).

fof(f103,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f128,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f216,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f215,f105])).

fof(f105,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f215,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f212,f130])).

fof(f130,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f212,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f66,f125])).

fof(f197,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f196,f138,f118,f192])).

fof(f118,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f196,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f189,f140])).

fof(f189,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f120,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f120,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f173,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f168,f138,f170])).

fof(f168,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f160,f83])).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f160,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f82,f140])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f167,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f162,f123,f164])).

fof(f162,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f159,f83])).

fof(f159,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f82,f125])).

fof(f157,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f152,f113,f154])).

fof(f113,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f152,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f115,f75])).

fof(f115,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f151,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f47,f148])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f146,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f48,f143])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f49,f138])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f136,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f50,f133])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f131,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f51,f128])).

fof(f51,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f52,f123])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f53,f118])).

fof(f53,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f54,f113])).

fof(f54,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f55,f108])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f56,f103])).

fof(f56,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f57,f98])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f58,f93])).

fof(f58,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:32:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (20253)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (20278)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (20270)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (20252)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (20259)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.53  % (20249)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.53  % (20255)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.53  % (20251)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (20250)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.54  % (20248)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (20256)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.54  % (20257)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.54  % (20274)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.54  % (20269)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.55  % (20264)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.55  % (20266)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.55  % (20277)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.55  % (20268)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.55  % (20272)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.43/0.55  % (20275)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (20258)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.56  % (20265)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.56  % (20263)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.43/0.56  % (20261)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.56  % (20267)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.56  % (20254)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (20270)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f714,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f157,f167,f173,f197,f221,f228,f238,f258,f278,f323,f340,f713])).
% 1.43/0.56  fof(f713,plain,(
% 1.43/0.56    spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_24 | ~spl4_29),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f712])).
% 1.43/0.56  fof(f712,plain,(
% 1.43/0.56    $false | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_24 | ~spl4_29)),
% 1.43/0.56    inference(trivial_inequality_removal,[],[f711])).
% 1.43/0.56  fof(f711,plain,(
% 1.43/0.56    k6_relat_1(sK1) != k6_relat_1(sK1) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_24 | ~spl4_29)),
% 1.43/0.56    inference(forward_demodulation,[],[f710,f194])).
% 1.43/0.56  fof(f194,plain,(
% 1.43/0.56    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 1.43/0.56    inference(avatar_component_clause,[],[f192])).
% 1.43/0.56  fof(f192,plain,(
% 1.43/0.56    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.43/0.56  fof(f710,plain,(
% 1.43/0.56    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(sK1) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_24 | ~spl4_29)),
% 1.43/0.56    inference(forward_demodulation,[],[f709,f235])).
% 1.43/0.56  fof(f235,plain,(
% 1.43/0.56    sK1 = k1_relat_1(sK3) | ~spl4_23),
% 1.43/0.56    inference(avatar_component_clause,[],[f233])).
% 1.43/0.56  fof(f233,plain,(
% 1.43/0.56    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.43/0.56  fof(f709,plain,(
% 1.43/0.56    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_29)),
% 1.43/0.56    inference(trivial_inequality_removal,[],[f708])).
% 1.43/0.56  fof(f708,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(sK0) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_29)),
% 1.43/0.56    inference(forward_demodulation,[],[f707,f255])).
% 1.43/0.56  fof(f255,plain,(
% 1.43/0.56    sK0 = k1_relat_1(sK2) | ~spl4_24),
% 1.43/0.56    inference(avatar_component_clause,[],[f253])).
% 1.43/0.56  fof(f253,plain,(
% 1.43/0.56    spl4_24 <=> sK0 = k1_relat_1(sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.43/0.56  fof(f707,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_29)),
% 1.43/0.56    inference(subsumption_resolution,[],[f706,f110])).
% 1.43/0.56  fof(f110,plain,(
% 1.43/0.56    v2_funct_1(sK2) | ~spl4_4),
% 1.43/0.56    inference(avatar_component_clause,[],[f108])).
% 1.43/0.56  fof(f108,plain,(
% 1.43/0.56    spl4_4 <=> v2_funct_1(sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.43/0.56  fof(f706,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_29)),
% 1.43/0.56    inference(subsumption_resolution,[],[f705,f172])).
% 1.43/0.56  fof(f172,plain,(
% 1.43/0.56    v1_relat_1(sK2) | ~spl4_15),
% 1.43/0.56    inference(avatar_component_clause,[],[f170])).
% 1.43/0.56  fof(f170,plain,(
% 1.43/0.56    spl4_15 <=> v1_relat_1(sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.43/0.56  fof(f705,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_29)),
% 1.43/0.56    inference(subsumption_resolution,[],[f704,f150])).
% 1.43/0.56  fof(f150,plain,(
% 1.43/0.56    v1_funct_1(sK2) | ~spl4_12),
% 1.43/0.56    inference(avatar_component_clause,[],[f148])).
% 1.43/0.56  fof(f148,plain,(
% 1.43/0.56    spl4_12 <=> v1_funct_1(sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.43/0.56  fof(f704,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_14 | ~spl4_29)),
% 1.43/0.56    inference(subsumption_resolution,[],[f703,f166])).
% 1.43/0.56  fof(f166,plain,(
% 1.43/0.56    v1_relat_1(sK3) | ~spl4_14),
% 1.43/0.56    inference(avatar_component_clause,[],[f164])).
% 1.43/0.56  fof(f164,plain,(
% 1.43/0.56    spl4_14 <=> v1_relat_1(sK3)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.43/0.56  fof(f703,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_29)),
% 1.43/0.56    inference(subsumption_resolution,[],[f702,f135])).
% 1.43/0.56  fof(f135,plain,(
% 1.43/0.56    v1_funct_1(sK3) | ~spl4_9),
% 1.43/0.56    inference(avatar_component_clause,[],[f133])).
% 1.43/0.56  fof(f133,plain,(
% 1.43/0.56    spl4_9 <=> v1_funct_1(sK3)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.43/0.56  fof(f702,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | (spl4_1 | ~spl4_29)),
% 1.43/0.56    inference(subsumption_resolution,[],[f697,f95])).
% 1.43/0.56  fof(f95,plain,(
% 1.43/0.56    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.43/0.56    inference(avatar_component_clause,[],[f93])).
% 1.43/0.56  fof(f93,plain,(
% 1.43/0.56    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.43/0.56  fof(f697,plain,(
% 1.43/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | ~spl4_29),
% 1.43/0.56    inference(superposition,[],[f384,f322])).
% 1.43/0.56  fof(f322,plain,(
% 1.43/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_29),
% 1.43/0.56    inference(avatar_component_clause,[],[f320])).
% 1.43/0.56  fof(f320,plain,(
% 1.43/0.56    spl4_29 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.43/0.56  fof(f384,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f382])).
% 1.43/0.56  fof(f382,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k6_relat_1(k1_relat_1(X1)) | k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(superposition,[],[f289,f60])).
% 1.43/0.56  fof(f60,plain,(
% 1.43/0.56    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f22])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(flattening,[],[f21])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,axiom,(
% 1.43/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.43/0.56  fof(f289,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k2_funct_1(X0),X1) | k2_funct_1(X0) = X2 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f288,f63])).
% 1.43/0.56  fof(f63,plain,(
% 1.43/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(flattening,[],[f25])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.43/0.56  fof(f288,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X2 | k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k2_funct_1(X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(subsumption_resolution,[],[f281,f64])).
% 1.43/0.56  fof(f64,plain,(
% 1.43/0.56    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f26])).
% 1.43/0.56  fof(f281,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X2 | k6_relat_1(k1_relat_1(X2)) != k5_relat_1(k2_funct_1(X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(superposition,[],[f90,f62])).
% 1.43/0.56  fof(f62,plain,(
% 1.43/0.56    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f24])).
% 1.43/0.56  fof(f24,plain,(
% 1.43/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(flattening,[],[f23])).
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.43/0.56  fof(f90,plain,(
% 1.43/0.56    ( ! [X2,X3,X1] : (k5_relat_1(X2,X3) != k6_relat_1(k2_relat_1(X1)) | X1 = X3 | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(equality_resolution,[],[f77])).
% 1.43/0.56  fof(f77,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f34])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f33])).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.43/0.56    inference(ennf_transformation,[],[f4])).
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).
% 1.43/0.56  fof(f340,plain,(
% 1.43/0.56    ~spl4_7 | ~spl4_10 | spl4_28),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f328])).
% 1.43/0.56  fof(f328,plain,(
% 1.43/0.56    $false | (~spl4_7 | ~spl4_10 | spl4_28)),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f140,f125,f318,f266])).
% 1.43/0.56  fof(f266,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f265])).
% 1.43/0.56  fof(f265,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(superposition,[],[f79,f80])).
% 1.43/0.56  fof(f80,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f39])).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(flattening,[],[f38])).
% 1.43/0.56  fof(f38,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.43/0.56    inference(ennf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.43/0.56  fof(f79,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f37])).
% 1.43/0.56  fof(f37,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(flattening,[],[f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.43/0.56    inference(ennf_transformation,[],[f7])).
% 1.43/0.56  fof(f7,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 1.43/0.56  fof(f318,plain,(
% 1.43/0.56    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_28),
% 1.43/0.56    inference(avatar_component_clause,[],[f316])).
% 1.43/0.56  fof(f316,plain,(
% 1.43/0.56    spl4_28 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.43/0.56  fof(f125,plain,(
% 1.43/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.43/0.56    inference(avatar_component_clause,[],[f123])).
% 1.43/0.56  fof(f123,plain,(
% 1.43/0.56    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.43/0.56  fof(f140,plain,(
% 1.43/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.43/0.56    inference(avatar_component_clause,[],[f138])).
% 1.43/0.56  fof(f138,plain,(
% 1.43/0.56    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.43/0.56  fof(f323,plain,(
% 1.43/0.56    ~spl4_28 | spl4_29 | ~spl4_25),
% 1.43/0.56    inference(avatar_split_clause,[],[f304,f275,f320,f316])).
% 1.43/0.56  fof(f275,plain,(
% 1.43/0.56    spl4_25 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.43/0.56  fof(f304,plain,(
% 1.43/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_25),
% 1.43/0.56    inference(resolution,[],[f246,f277])).
% 1.43/0.56  fof(f277,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_25),
% 1.43/0.56    inference(avatar_component_clause,[],[f275])).
% 1.43/0.56  fof(f246,plain,(
% 1.43/0.56    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.43/0.56    inference(resolution,[],[f72,f158])).
% 1.43/0.56  fof(f158,plain,(
% 1.43/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.43/0.56    inference(forward_demodulation,[],[f74,f75])).
% 1.43/0.56  fof(f75,plain,(
% 1.43/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,axiom,(
% 1.43/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.43/0.56  fof(f74,plain,(
% 1.43/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,plain,(
% 1.43/0.56    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.43/0.56    inference(pure_predicate_removal,[],[f13])).
% 1.43/0.56  fof(f13,axiom,(
% 1.43/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.43/0.56  fof(f72,plain,(
% 1.43/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f46])).
% 1.43/0.56  fof(f46,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(nnf_transformation,[],[f30])).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(flattening,[],[f29])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.43/0.56    inference(ennf_transformation,[],[f11])).
% 1.43/0.56  fof(f11,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.43/0.56  fof(f278,plain,(
% 1.43/0.56    spl4_25 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.43/0.56    inference(avatar_split_clause,[],[f273,f154,f148,f138,f133,f123,f275])).
% 1.43/0.56  fof(f154,plain,(
% 1.43/0.56    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.43/0.56  fof(f273,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.43/0.56    inference(subsumption_resolution,[],[f272,f150])).
% 1.43/0.56  fof(f272,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.43/0.56    inference(subsumption_resolution,[],[f271,f140])).
% 1.43/0.56  fof(f271,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.43/0.56    inference(subsumption_resolution,[],[f270,f135])).
% 1.43/0.56  fof(f270,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.43/0.56    inference(subsumption_resolution,[],[f269,f125])).
% 1.43/0.56  fof(f269,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.43/0.56    inference(superposition,[],[f156,f76])).
% 1.43/0.56  fof(f76,plain,(
% 1.43/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f32])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.43/0.56    inference(flattening,[],[f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.43/0.56    inference(ennf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,axiom,(
% 1.43/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.43/0.56  fof(f156,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.43/0.56    inference(avatar_component_clause,[],[f154])).
% 1.43/0.56  fof(f258,plain,(
% 1.43/0.56    spl4_24 | ~spl4_10 | ~spl4_22),
% 1.43/0.56    inference(avatar_split_clause,[],[f257,f225,f138,f253])).
% 1.43/0.56  fof(f225,plain,(
% 1.43/0.56    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.43/0.56  fof(f257,plain,(
% 1.43/0.56    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_22)),
% 1.43/0.56    inference(subsumption_resolution,[],[f249,f140])).
% 1.43/0.56  fof(f249,plain,(
% 1.43/0.56    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_22),
% 1.43/0.56    inference(superposition,[],[f81,f227])).
% 1.43/0.56  fof(f227,plain,(
% 1.43/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_22),
% 1.43/0.56    inference(avatar_component_clause,[],[f225])).
% 1.43/0.56  fof(f81,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f40])).
% 1.43/0.56  fof(f40,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f8])).
% 1.43/0.56  fof(f8,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.43/0.56  fof(f238,plain,(
% 1.43/0.56    spl4_23 | ~spl4_7 | ~spl4_21),
% 1.43/0.56    inference(avatar_split_clause,[],[f237,f218,f123,f233])).
% 1.43/0.56  fof(f218,plain,(
% 1.43/0.56    spl4_21 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.43/0.56  fof(f237,plain,(
% 1.43/0.56    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_21)),
% 1.43/0.56    inference(subsumption_resolution,[],[f230,f125])).
% 1.43/0.56  fof(f230,plain,(
% 1.43/0.56    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_21),
% 1.43/0.56    inference(superposition,[],[f81,f220])).
% 1.43/0.56  fof(f220,plain,(
% 1.43/0.56    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_21),
% 1.43/0.56    inference(avatar_component_clause,[],[f218])).
% 1.43/0.56  fof(f228,plain,(
% 1.43/0.56    spl4_22 | spl4_2 | ~spl4_10 | ~spl4_11),
% 1.43/0.56    inference(avatar_split_clause,[],[f223,f143,f138,f98,f225])).
% 1.43/0.56  fof(f98,plain,(
% 1.43/0.56    spl4_2 <=> k1_xboole_0 = sK1),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.43/0.56  fof(f143,plain,(
% 1.43/0.56    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.43/0.56  fof(f223,plain,(
% 1.43/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 1.43/0.56    inference(subsumption_resolution,[],[f222,f100])).
% 1.43/0.56  fof(f100,plain,(
% 1.43/0.56    k1_xboole_0 != sK1 | spl4_2),
% 1.43/0.56    inference(avatar_component_clause,[],[f98])).
% 1.43/0.56  fof(f222,plain,(
% 1.43/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 1.43/0.56    inference(subsumption_resolution,[],[f213,f145])).
% 1.43/0.56  fof(f145,plain,(
% 1.43/0.56    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.43/0.56    inference(avatar_component_clause,[],[f143])).
% 1.43/0.56  fof(f213,plain,(
% 1.43/0.56    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 1.43/0.56    inference(resolution,[],[f66,f140])).
% 1.43/0.56  fof(f66,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f45])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(nnf_transformation,[],[f28])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(flattening,[],[f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f12])).
% 1.43/0.56  fof(f12,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.43/0.56  fof(f221,plain,(
% 1.43/0.56    spl4_21 | spl4_3 | ~spl4_7 | ~spl4_8),
% 1.43/0.56    inference(avatar_split_clause,[],[f216,f128,f123,f103,f218])).
% 1.43/0.56  fof(f103,plain,(
% 1.43/0.56    spl4_3 <=> k1_xboole_0 = sK0),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.43/0.56  fof(f128,plain,(
% 1.43/0.56    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.43/0.56  fof(f216,plain,(
% 1.43/0.56    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 1.43/0.56    inference(subsumption_resolution,[],[f215,f105])).
% 1.43/0.56  fof(f105,plain,(
% 1.43/0.56    k1_xboole_0 != sK0 | spl4_3),
% 1.43/0.56    inference(avatar_component_clause,[],[f103])).
% 1.43/0.56  fof(f215,plain,(
% 1.43/0.56    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 1.43/0.56    inference(subsumption_resolution,[],[f212,f130])).
% 1.43/0.56  fof(f130,plain,(
% 1.43/0.56    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.43/0.56    inference(avatar_component_clause,[],[f128])).
% 1.43/0.56  fof(f212,plain,(
% 1.43/0.56    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 1.43/0.56    inference(resolution,[],[f66,f125])).
% 1.43/0.56  fof(f197,plain,(
% 1.43/0.56    spl4_18 | ~spl4_6 | ~spl4_10),
% 1.43/0.56    inference(avatar_split_clause,[],[f196,f138,f118,f192])).
% 1.43/0.56  fof(f118,plain,(
% 1.43/0.56    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.43/0.56  fof(f196,plain,(
% 1.43/0.56    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 1.43/0.56    inference(subsumption_resolution,[],[f189,f140])).
% 1.43/0.56  fof(f189,plain,(
% 1.43/0.56    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 1.43/0.56    inference(superposition,[],[f120,f78])).
% 1.43/0.56  fof(f78,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f35])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.56    inference(ennf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.43/0.56  fof(f120,plain,(
% 1.43/0.56    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.43/0.56    inference(avatar_component_clause,[],[f118])).
% 1.43/0.56  fof(f173,plain,(
% 1.43/0.56    spl4_15 | ~spl4_10),
% 1.43/0.56    inference(avatar_split_clause,[],[f168,f138,f170])).
% 1.43/0.56  fof(f168,plain,(
% 1.43/0.56    v1_relat_1(sK2) | ~spl4_10),
% 1.43/0.56    inference(subsumption_resolution,[],[f160,f83])).
% 1.43/0.56  fof(f83,plain,(
% 1.43/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f2])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.43/0.56  fof(f160,plain,(
% 1.43/0.56    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 1.43/0.56    inference(resolution,[],[f82,f140])).
% 1.43/0.56  fof(f82,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f41])).
% 1.43/0.56  fof(f41,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f1])).
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.43/0.56  fof(f167,plain,(
% 1.43/0.56    spl4_14 | ~spl4_7),
% 1.43/0.56    inference(avatar_split_clause,[],[f162,f123,f164])).
% 1.43/0.56  fof(f162,plain,(
% 1.43/0.56    v1_relat_1(sK3) | ~spl4_7),
% 1.43/0.56    inference(subsumption_resolution,[],[f159,f83])).
% 1.43/0.56  fof(f159,plain,(
% 1.43/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 1.43/0.56    inference(resolution,[],[f82,f125])).
% 1.43/0.56  fof(f157,plain,(
% 1.43/0.56    spl4_13 | ~spl4_5),
% 1.43/0.56    inference(avatar_split_clause,[],[f152,f113,f154])).
% 1.43/0.56  fof(f113,plain,(
% 1.43/0.56    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.43/0.56  fof(f152,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.43/0.56    inference(backward_demodulation,[],[f115,f75])).
% 1.43/0.56  fof(f115,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.43/0.56    inference(avatar_component_clause,[],[f113])).
% 1.43/0.56  fof(f151,plain,(
% 1.43/0.56    spl4_12),
% 1.43/0.56    inference(avatar_split_clause,[],[f47,f148])).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    v1_funct_1(sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f43,f42])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f43,plain,(
% 1.43/0.56    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f20,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.43/0.56    inference(flattening,[],[f19])).
% 1.43/0.56  fof(f19,plain,(
% 1.43/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.43/0.56    inference(ennf_transformation,[],[f17])).
% 1.43/0.56  fof(f17,negated_conjecture,(
% 1.43/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.43/0.56    inference(negated_conjecture,[],[f16])).
% 1.43/0.56  fof(f16,conjecture,(
% 1.43/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.43/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.43/0.56  fof(f146,plain,(
% 1.43/0.56    spl4_11),
% 1.43/0.56    inference(avatar_split_clause,[],[f48,f143])).
% 1.43/0.56  fof(f48,plain,(
% 1.43/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f141,plain,(
% 1.43/0.56    spl4_10),
% 1.43/0.56    inference(avatar_split_clause,[],[f49,f138])).
% 1.43/0.56  fof(f49,plain,(
% 1.43/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f136,plain,(
% 1.43/0.56    spl4_9),
% 1.43/0.56    inference(avatar_split_clause,[],[f50,f133])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    v1_funct_1(sK3)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f131,plain,(
% 1.43/0.56    spl4_8),
% 1.43/0.56    inference(avatar_split_clause,[],[f51,f128])).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    v1_funct_2(sK3,sK1,sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f126,plain,(
% 1.43/0.56    spl4_7),
% 1.43/0.56    inference(avatar_split_clause,[],[f52,f123])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f121,plain,(
% 1.43/0.56    spl4_6),
% 1.43/0.56    inference(avatar_split_clause,[],[f53,f118])).
% 1.43/0.56  fof(f53,plain,(
% 1.43/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f116,plain,(
% 1.43/0.56    spl4_5),
% 1.43/0.56    inference(avatar_split_clause,[],[f54,f113])).
% 1.43/0.56  fof(f54,plain,(
% 1.43/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f111,plain,(
% 1.43/0.56    spl4_4),
% 1.43/0.56    inference(avatar_split_clause,[],[f55,f108])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    v2_funct_1(sK2)),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f106,plain,(
% 1.43/0.56    ~spl4_3),
% 1.43/0.56    inference(avatar_split_clause,[],[f56,f103])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    k1_xboole_0 != sK0),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f101,plain,(
% 1.43/0.56    ~spl4_2),
% 1.43/0.56    inference(avatar_split_clause,[],[f57,f98])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    k1_xboole_0 != sK1),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  fof(f96,plain,(
% 1.43/0.56    ~spl4_1),
% 1.43/0.56    inference(avatar_split_clause,[],[f58,f93])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    k2_funct_1(sK2) != sK3),
% 1.43/0.56    inference(cnf_transformation,[],[f44])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (20270)------------------------------
% 1.43/0.56  % (20270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (20270)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (20270)Memory used [KB]: 6908
% 1.43/0.56  % (20270)Time elapsed: 0.152 s
% 1.43/0.56  % (20270)------------------------------
% 1.43/0.56  % (20270)------------------------------
% 1.43/0.56  % (20262)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.56  % (20246)Success in time 0.197 s
%------------------------------------------------------------------------------
