%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:55 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 609 expanded)
%              Number of leaves         :   39 ( 197 expanded)
%              Depth                    :   22
%              Number of atoms          :  641 (4039 expanded)
%              Number of equality atoms :  104 ( 165 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f161,f188,f191,f255,f1243,f1256,f1307,f1419,f1426,f1485,f1508])).

fof(f1508,plain,
    ( spl8_2
    | ~ spl8_5
    | ~ spl8_76 ),
    inference(avatar_contradiction_clause,[],[f1507])).

fof(f1507,plain,
    ( $false
    | spl8_2
    | ~ spl8_5
    | ~ spl8_76 ),
    inference(subsumption_resolution,[],[f1506,f164])).

fof(f164,plain,
    ( v1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl8_5
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1506,plain,
    ( ~ v1_relat_1(sK5)
    | spl8_2
    | ~ spl8_76 ),
    inference(subsumption_resolution,[],[f1499,f142])).

fof(f142,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_2
  <=> v2_funct_2(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1499,plain,
    ( v2_funct_2(sK5,sK2)
    | ~ v1_relat_1(sK5)
    | ~ spl8_76 ),
    inference(superposition,[],[f314,f1255])).

fof(f1255,plain,
    ( sK2 = k2_relat_1(sK5)
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f1253])).

fof(f1253,plain,
    ( spl8_76
  <=> sK2 = k2_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f314,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f127,f212])).

fof(f212,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f102,f128])).

fof(f128,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f127,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1485,plain,
    ( ~ spl8_5
    | spl8_75 ),
    inference(avatar_contradiction_clause,[],[f1484])).

fof(f1484,plain,
    ( $false
    | ~ spl8_5
    | spl8_75 ),
    inference(subsumption_resolution,[],[f1483,f164])).

fof(f1483,plain,
    ( ~ v1_relat_1(sK5)
    | spl8_75 ),
    inference(subsumption_resolution,[],[f1482,f235])).

fof(f235,plain,(
    v5_relat_1(sK5,sK2) ),
    inference(resolution,[],[f114,f75])).

fof(f75,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ v2_funct_2(sK5,sK2)
      | ~ v2_funct_1(sK4) )
    & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f56,f55])).

fof(f55,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK2)
            | ~ v2_funct_1(sK4) )
          & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
          & v1_funct_2(X3,sK3,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK2)
          | ~ v2_funct_1(sK4) )
        & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        & v1_funct_2(X3,sK3,sK2)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK5,sK2)
        | ~ v2_funct_1(sK4) )
      & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      & v1_funct_2(sK5,sK3,sK2)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1482,plain,
    ( ~ v5_relat_1(sK5,sK2)
    | ~ v1_relat_1(sK5)
    | spl8_75 ),
    inference(resolution,[],[f1251,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1251,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK2)
    | spl8_75 ),
    inference(avatar_component_clause,[],[f1249])).

fof(f1249,plain,
    ( spl8_75
  <=> r1_tarski(k2_relat_1(sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f1426,plain,
    ( spl8_1
    | spl8_73
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f1425,f1212,f1208,f136])).

fof(f136,plain,
    ( spl8_1
  <=> v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1208,plain,
    ( spl8_73
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f1212,plain,
    ( spl8_74
  <=> v2_funct_1(k5_relat_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f1425,plain,
    ( ~ v2_funct_1(k5_relat_1(sK4,sK5))
    | k1_xboole_0 = sK2
    | v2_funct_1(sK4) ),
    inference(global_subsumption,[],[f70,f71,f74,f72,f75,f1424])).

fof(f1424,plain,
    ( ~ v2_funct_1(k5_relat_1(sK4,sK5))
    | k1_xboole_0 = sK2
    | v2_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f1187,f73])).

fof(f73,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f1187,plain,
    ( ~ v2_funct_1(k5_relat_1(sK4,sK5))
    | k1_xboole_0 = sK2
    | v2_funct_1(sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(sK5,sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(sK4,sK2,sK3)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f116,f856])).

fof(f856,plain,(
    k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f851,f70])).

fof(f851,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f433,f72])).

fof(f433,plain,(
    ! [X14,X12,X13] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | k1_partfun1(X12,X13,sK3,sK2,X14,sK5) = k5_relat_1(X14,sK5)
      | ~ v1_funct_1(X14) ) ),
    inference(subsumption_resolution,[],[f421,f73])).

fof(f421,plain,(
    ! [X14,X12,X13] :
      ( k1_partfun1(X12,X13,sK3,sK2,X14,sK5) = k5_relat_1(X14,sK5)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ v1_funct_1(X14) ) ),
    inference(resolution,[],[f120,f75])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f74,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f71,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f1419,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f1418])).

fof(f1418,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1383,f178])).

fof(f178,plain,(
    sP0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f177,f147])).

fof(f147,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f100,f130])).

fof(f130,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f100,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f177,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
    | sP0(k1_xboole_0) ),
    inference(superposition,[],[f94,f171])).

fof(f171,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f145,f78])).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f145,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f90,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f90,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK6(X0) != sK7(X0)
          & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0))
          & r2_hidden(sK6(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK6(X0) != sK7(X0)
        & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1383,plain,
    ( ~ sP0(k1_xboole_0)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_10 ),
    inference(backward_demodulation,[],[f196,f1321])).

fof(f1321,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_10 ),
    inference(resolution,[],[f254,f89])).

fof(f254,plain,
    ( v1_xboole_0(sK4)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl8_10
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f196,plain,
    ( ~ sP0(sK4)
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f194,f138])).

fof(f138,plain,
    ( ~ v2_funct_1(sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f194,plain,
    ( ~ sP0(sK4)
    | v2_funct_1(sK4)
    | ~ spl8_4 ),
    inference(resolution,[],[f160,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f160,plain,
    ( sP1(sK4)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl8_4
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1307,plain,
    ( spl8_9
    | ~ spl8_73 ),
    inference(avatar_contradiction_clause,[],[f1306])).

fof(f1306,plain,
    ( $false
    | spl8_9
    | ~ spl8_73 ),
    inference(subsumption_resolution,[],[f1282,f78])).

fof(f1282,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_9
    | ~ spl8_73 ),
    inference(backward_demodulation,[],[f250,f1210])).

fof(f1210,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f250,plain,
    ( ~ v1_xboole_0(sK2)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl8_9
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f1256,plain,
    ( ~ spl8_75
    | spl8_76
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1247,f163,f154,f1253,f1249])).

fof(f154,plain,
    ( spl8_3
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1247,plain,
    ( sK2 = k2_relat_1(sK5)
    | ~ r1_tarski(k2_relat_1(sK5),sK2)
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f1246,f125])).

fof(f125,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f86,f80])).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f86,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1246,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK2)
    | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f1245,f125])).

fof(f1245,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(k6_partfun1(sK2)))
    | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f1244,f164])).

fof(f1244,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(k6_partfun1(sK2)))
    | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2))
    | ~ v1_relat_1(sK5)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f1239,f155])).

fof(f155,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f1239,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),k2_relat_1(k6_partfun1(sK2)))
    | ~ v1_relat_1(sK4)
    | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2))
    | ~ v1_relat_1(sK5) ),
    inference(superposition,[],[f324,f1217])).

fof(f1217,plain,(
    k6_partfun1(sK2) = k5_relat_1(sK4,sK5) ),
    inference(global_subsumption,[],[f1195,f1216])).

fof(f1216,plain,
    ( k6_partfun1(sK2) = k5_relat_1(sK4,sK5)
    | ~ m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(resolution,[],[f1183,f382])).

fof(f382,plain,(
    ! [X4,X3] :
      ( ~ r2_relset_1(X3,X3,X4,k6_partfun1(X3))
      | k6_partfun1(X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f118,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1183,plain,(
    r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK5),k6_partfun1(sK2)) ),
    inference(backward_demodulation,[],[f76,f856])).

fof(f76,plain,(
    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f1195,plain,(
    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(subsumption_resolution,[],[f1194,f70])).

fof(f1194,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f1193,f72])).

fof(f1193,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f1192,f73])).

fof(f1192,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f1185,f75])).

fof(f1185,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f122,f856])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f324,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f87,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1243,plain,(
    spl8_74 ),
    inference(avatar_contradiction_clause,[],[f1242])).

fof(f1242,plain,
    ( $false
    | spl8_74 ),
    inference(subsumption_resolution,[],[f1236,f123])).

fof(f123,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f82,f80])).

fof(f82,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1236,plain,
    ( ~ v2_funct_1(k6_partfun1(sK2))
    | spl8_74 ),
    inference(backward_demodulation,[],[f1214,f1217])).

fof(f1214,plain,
    ( ~ v2_funct_1(k5_relat_1(sK4,sK5))
    | spl8_74 ),
    inference(avatar_component_clause,[],[f1212])).

fof(f255,plain,
    ( ~ spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f243,f252,f248])).

fof(f243,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f103,f72])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f191,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f189,f99])).

fof(f99,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f189,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK2))
    | spl8_5 ),
    inference(subsumption_resolution,[],[f185,f165])).

fof(f165,plain,
    ( ~ v1_relat_1(sK5)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f185,plain,
    ( v1_relat_1(sK5)
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK2)) ),
    inference(resolution,[],[f88,f75])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f188,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f186,f99])).

fof(f186,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | spl8_3 ),
    inference(subsumption_resolution,[],[f184,f156])).

fof(f156,plain,
    ( ~ v1_relat_1(sK4)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f184,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f88,f72])).

fof(f161,plain,
    ( ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f151,f158,f154])).

fof(f151,plain,
    ( sP1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f98,f70])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f35,f53,f52])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f143,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f77,f140,f136])).

fof(f77,plain,
    ( ~ v2_funct_2(sK5,sK2)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:16:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.55  % (31389)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (31386)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.56  % (31397)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (31399)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.57  % (31391)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.57  % (31402)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.65/0.57  % (31394)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.65/0.57  % (31407)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.65/0.58  % (31405)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.65/0.58  % (31410)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.65/0.58  % (31387)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.65/0.58  % (31399)Refutation not found, incomplete strategy% (31399)------------------------------
% 1.65/0.58  % (31399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (31399)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (31399)Memory used [KB]: 10746
% 1.65/0.58  % (31399)Time elapsed: 0.144 s
% 1.65/0.58  % (31399)------------------------------
% 1.65/0.58  % (31399)------------------------------
% 1.80/0.59  % (31390)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.80/0.59  % (31395)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.80/0.59  % (31406)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.80/0.60  % (31403)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.80/0.60  % (31398)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.80/0.61  % (31384)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.80/0.61  % (31412)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.80/0.61  % (31383)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.80/0.61  % (31388)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.80/0.62  % (31400)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.80/0.62  % (31404)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.80/0.62  % (31408)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.80/0.62  % (31396)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.80/0.64  % (31411)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.80/0.64  % (31392)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.19/0.65  % (31393)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.19/0.66  % (31385)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 2.26/0.66  % (31411)Refutation not found, incomplete strategy% (31411)------------------------------
% 2.26/0.66  % (31411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.66  % (31411)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.66  
% 2.26/0.66  % (31411)Memory used [KB]: 10874
% 2.26/0.66  % (31411)Time elapsed: 0.246 s
% 2.26/0.66  % (31411)------------------------------
% 2.26/0.66  % (31411)------------------------------
% 2.26/0.66  % (31409)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.26/0.67  % (31401)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.26/0.68  % (31393)Refutation not found, incomplete strategy% (31393)------------------------------
% 2.26/0.68  % (31393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.68  % (31393)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.68  
% 2.26/0.68  % (31393)Memory used [KB]: 10874
% 2.26/0.68  % (31393)Time elapsed: 0.256 s
% 2.26/0.68  % (31393)------------------------------
% 2.26/0.68  % (31393)------------------------------
% 2.26/0.68  % (31389)Refutation found. Thanks to Tanya!
% 2.26/0.68  % SZS status Theorem for theBenchmark
% 2.26/0.68  % SZS output start Proof for theBenchmark
% 2.26/0.68  fof(f1511,plain,(
% 2.26/0.68    $false),
% 2.26/0.68    inference(avatar_sat_refutation,[],[f143,f161,f188,f191,f255,f1243,f1256,f1307,f1419,f1426,f1485,f1508])).
% 2.26/0.68  fof(f1508,plain,(
% 2.26/0.68    spl8_2 | ~spl8_5 | ~spl8_76),
% 2.26/0.68    inference(avatar_contradiction_clause,[],[f1507])).
% 2.26/0.68  fof(f1507,plain,(
% 2.26/0.68    $false | (spl8_2 | ~spl8_5 | ~spl8_76)),
% 2.26/0.68    inference(subsumption_resolution,[],[f1506,f164])).
% 2.26/0.68  fof(f164,plain,(
% 2.26/0.68    v1_relat_1(sK5) | ~spl8_5),
% 2.26/0.68    inference(avatar_component_clause,[],[f163])).
% 2.26/0.68  fof(f163,plain,(
% 2.26/0.68    spl8_5 <=> v1_relat_1(sK5)),
% 2.26/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.26/0.68  fof(f1506,plain,(
% 2.26/0.68    ~v1_relat_1(sK5) | (spl8_2 | ~spl8_76)),
% 2.26/0.68    inference(subsumption_resolution,[],[f1499,f142])).
% 2.26/0.68  fof(f142,plain,(
% 2.26/0.68    ~v2_funct_2(sK5,sK2) | spl8_2),
% 2.26/0.68    inference(avatar_component_clause,[],[f140])).
% 2.26/0.68  fof(f140,plain,(
% 2.26/0.68    spl8_2 <=> v2_funct_2(sK5,sK2)),
% 2.26/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.26/0.68  fof(f1499,plain,(
% 2.26/0.68    v2_funct_2(sK5,sK2) | ~v1_relat_1(sK5) | ~spl8_76),
% 2.26/0.68    inference(superposition,[],[f314,f1255])).
% 2.26/0.68  fof(f1255,plain,(
% 2.26/0.68    sK2 = k2_relat_1(sK5) | ~spl8_76),
% 2.26/0.68    inference(avatar_component_clause,[],[f1253])).
% 2.26/0.68  fof(f1253,plain,(
% 2.26/0.68    spl8_76 <=> sK2 = k2_relat_1(sK5)),
% 2.26/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).
% 2.26/0.68  fof(f314,plain,(
% 2.26/0.68    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f127,f212])).
% 2.26/0.68  fof(f212,plain,(
% 2.26/0.68    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.26/0.68    inference(resolution,[],[f102,f128])).
% 2.26/0.68  fof(f128,plain,(
% 2.26/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.26/0.68    inference(equality_resolution,[],[f108])).
% 2.26/0.68  fof(f108,plain,(
% 2.26/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.26/0.68    inference(cnf_transformation,[],[f66])).
% 2.26/0.68  fof(f66,plain,(
% 2.26/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.26/0.68    inference(flattening,[],[f65])).
% 2.26/0.68  fof(f65,plain,(
% 2.26/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.26/0.68    inference(nnf_transformation,[],[f3])).
% 2.26/0.68  fof(f3,axiom,(
% 2.26/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.26/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.26/0.68  fof(f102,plain,(
% 2.26/0.68    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f63])).
% 2.26/0.68  fof(f63,plain,(
% 2.26/0.68    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.26/0.68    inference(nnf_transformation,[],[f36])).
% 2.26/0.68  fof(f36,plain,(
% 2.26/0.68    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.26/0.68    inference(ennf_transformation,[],[f9])).
% 2.26/0.68  fof(f9,axiom,(
% 2.26/0.68    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.26/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.26/0.68  fof(f127,plain,(
% 2.26/0.68    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.26/0.68    inference(equality_resolution,[],[f106])).
% 2.26/0.68  fof(f106,plain,(
% 2.26/0.68    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f64])).
% 2.26/0.68  fof(f64,plain,(
% 2.26/0.68    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.26/0.68    inference(nnf_transformation,[],[f40])).
% 2.26/0.68  fof(f40,plain,(
% 2.26/0.68    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.26/0.68    inference(flattening,[],[f39])).
% 2.26/0.68  fof(f39,plain,(
% 2.26/0.68    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.26/0.68    inference(ennf_transformation,[],[f20])).
% 2.26/0.68  fof(f20,axiom,(
% 2.26/0.68    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.26/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 2.26/0.68  fof(f1485,plain,(
% 2.26/0.68    ~spl8_5 | spl8_75),
% 2.26/0.68    inference(avatar_contradiction_clause,[],[f1484])).
% 2.26/0.68  fof(f1484,plain,(
% 2.26/0.68    $false | (~spl8_5 | spl8_75)),
% 2.26/0.68    inference(subsumption_resolution,[],[f1483,f164])).
% 2.26/0.68  fof(f1483,plain,(
% 2.26/0.68    ~v1_relat_1(sK5) | spl8_75),
% 2.26/0.68    inference(subsumption_resolution,[],[f1482,f235])).
% 2.26/0.68  fof(f235,plain,(
% 2.26/0.68    v5_relat_1(sK5,sK2)),
% 2.26/0.68    inference(resolution,[],[f114,f75])).
% 2.26/0.68  fof(f75,plain,(
% 2.26/0.68    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 2.26/0.68    inference(cnf_transformation,[],[f57])).
% 2.26/0.68  fof(f57,plain,(
% 2.26/0.68    ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.26/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f56,f55])).
% 2.26/0.68  fof(f55,plain,(
% 2.26/0.68    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.26/0.68    introduced(choice_axiom,[])).
% 2.26/0.68  fof(f56,plain,(
% 2.26/0.68    ? [X3] : ((~v2_funct_2(X3,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,X3),k6_partfun1(sK2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(X3,sK3,sK2) & v1_funct_1(X3)) => ((~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)) & r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5))),
% 2.26/0.68    introduced(choice_axiom,[])).
% 2.26/0.68  fof(f29,plain,(
% 2.26/0.68    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.26/0.68    inference(flattening,[],[f28])).
% 2.26/0.68  fof(f28,plain,(
% 2.26/0.68    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.26/0.68    inference(ennf_transformation,[],[f27])).
% 2.26/0.68  fof(f27,negated_conjecture,(
% 2.26/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.26/0.68    inference(negated_conjecture,[],[f26])).
% 2.26/0.68  fof(f26,conjecture,(
% 2.26/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.26/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 2.26/0.68  fof(f114,plain,(
% 2.26/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f41])).
% 2.26/0.68  fof(f41,plain,(
% 2.26/0.68    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.68    inference(ennf_transformation,[],[f16])).
% 2.26/0.68  fof(f16,axiom,(
% 2.26/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.26/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.26/0.68  fof(f1482,plain,(
% 2.26/0.68    ~v5_relat_1(sK5,sK2) | ~v1_relat_1(sK5) | spl8_75),
% 2.26/0.68    inference(resolution,[],[f1251,f101])).
% 2.26/0.68  fof(f101,plain,(
% 2.26/0.68    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f63])).
% 2.26/0.68  fof(f1251,plain,(
% 2.26/0.68    ~r1_tarski(k2_relat_1(sK5),sK2) | spl8_75),
% 2.26/0.68    inference(avatar_component_clause,[],[f1249])).
% 2.26/0.68  fof(f1249,plain,(
% 2.26/0.68    spl8_75 <=> r1_tarski(k2_relat_1(sK5),sK2)),
% 2.26/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).
% 2.26/0.68  fof(f1426,plain,(
% 2.26/0.68    spl8_1 | spl8_73 | ~spl8_74),
% 2.26/0.68    inference(avatar_split_clause,[],[f1425,f1212,f1208,f136])).
% 2.26/0.68  fof(f136,plain,(
% 2.26/0.68    spl8_1 <=> v2_funct_1(sK4)),
% 2.26/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.26/0.68  fof(f1208,plain,(
% 2.26/0.68    spl8_73 <=> k1_xboole_0 = sK2),
% 2.26/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).
% 2.26/0.68  fof(f1212,plain,(
% 2.26/0.68    spl8_74 <=> v2_funct_1(k5_relat_1(sK4,sK5))),
% 2.26/0.68    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).
% 2.26/0.68  fof(f1425,plain,(
% 2.26/0.68    ~v2_funct_1(k5_relat_1(sK4,sK5)) | k1_xboole_0 = sK2 | v2_funct_1(sK4)),
% 2.26/0.68    inference(global_subsumption,[],[f70,f71,f74,f72,f75,f1424])).
% 2.26/0.68  fof(f1424,plain,(
% 2.26/0.68    ~v2_funct_1(k5_relat_1(sK4,sK5)) | k1_xboole_0 = sK2 | v2_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4)),
% 2.26/0.68    inference(subsumption_resolution,[],[f1187,f73])).
% 2.26/0.68  fof(f73,plain,(
% 2.26/0.68    v1_funct_1(sK5)),
% 2.26/0.68    inference(cnf_transformation,[],[f57])).
% 2.26/0.68  fof(f1187,plain,(
% 2.26/0.68    ~v2_funct_1(k5_relat_1(sK4,sK5)) | k1_xboole_0 = sK2 | v2_funct_1(sK4) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(sK5,sK3,sK2) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(sK4,sK2,sK3) | ~v1_funct_1(sK4)),
% 2.26/0.68    inference(superposition,[],[f116,f856])).
% 2.26/0.68  fof(f856,plain,(
% 2.26/0.68    k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)),
% 2.26/0.68    inference(subsumption_resolution,[],[f851,f70])).
% 2.26/0.68  fof(f851,plain,(
% 2.26/0.68    k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) | ~v1_funct_1(sK4)),
% 2.26/0.68    inference(resolution,[],[f433,f72])).
% 2.26/0.68  fof(f433,plain,(
% 2.26/0.68    ( ! [X14,X12,X13] : (~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | k1_partfun1(X12,X13,sK3,sK2,X14,sK5) = k5_relat_1(X14,sK5) | ~v1_funct_1(X14)) )),
% 2.26/0.68    inference(subsumption_resolution,[],[f421,f73])).
% 2.26/0.68  fof(f421,plain,(
% 2.26/0.68    ( ! [X14,X12,X13] : (k1_partfun1(X12,X13,sK3,sK2,X14,sK5) = k5_relat_1(X14,sK5) | ~v1_funct_1(sK5) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_1(X14)) )),
% 2.26/0.68    inference(resolution,[],[f120,f75])).
% 2.26/0.68  fof(f120,plain,(
% 2.26/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f49])).
% 2.26/0.68  fof(f49,plain,(
% 2.26/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.26/0.68    inference(flattening,[],[f48])).
% 2.26/0.68  fof(f48,plain,(
% 2.26/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.26/0.68    inference(ennf_transformation,[],[f23])).
% 2.26/0.68  fof(f23,axiom,(
% 2.26/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.26/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.26/0.68  fof(f116,plain,(
% 2.26/0.68    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.26/0.68    inference(cnf_transformation,[],[f45])).
% 2.26/0.68  fof(f45,plain,(
% 2.26/0.68    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.26/0.68    inference(flattening,[],[f44])).
% 2.26/0.70  fof(f44,plain,(
% 2.26/0.70    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.26/0.70    inference(ennf_transformation,[],[f25])).
% 2.26/0.70  fof(f25,axiom,(
% 2.26/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 2.26/0.70  fof(f72,plain,(
% 2.26/0.70    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.26/0.70    inference(cnf_transformation,[],[f57])).
% 2.26/0.70  fof(f74,plain,(
% 2.26/0.70    v1_funct_2(sK5,sK3,sK2)),
% 2.26/0.70    inference(cnf_transformation,[],[f57])).
% 2.26/0.70  fof(f71,plain,(
% 2.26/0.70    v1_funct_2(sK4,sK2,sK3)),
% 2.26/0.70    inference(cnf_transformation,[],[f57])).
% 2.26/0.70  fof(f70,plain,(
% 2.26/0.70    v1_funct_1(sK4)),
% 2.26/0.70    inference(cnf_transformation,[],[f57])).
% 2.26/0.70  fof(f1419,plain,(
% 2.26/0.70    spl8_1 | ~spl8_4 | ~spl8_10),
% 2.26/0.70    inference(avatar_contradiction_clause,[],[f1418])).
% 2.26/0.70  fof(f1418,plain,(
% 2.26/0.70    $false | (spl8_1 | ~spl8_4 | ~spl8_10)),
% 2.26/0.70    inference(subsumption_resolution,[],[f1383,f178])).
% 2.26/0.70  fof(f178,plain,(
% 2.26/0.70    sP0(k1_xboole_0)),
% 2.26/0.70    inference(subsumption_resolution,[],[f177,f147])).
% 2.26/0.70  fof(f147,plain,(
% 2.26/0.70    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.26/0.70    inference(superposition,[],[f100,f130])).
% 2.26/0.70  fof(f130,plain,(
% 2.26/0.70    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.26/0.70    inference(equality_resolution,[],[f112])).
% 2.26/0.70  fof(f112,plain,(
% 2.26/0.70    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.26/0.70    inference(cnf_transformation,[],[f68])).
% 2.26/0.70  fof(f68,plain,(
% 2.26/0.70    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.26/0.70    inference(flattening,[],[f67])).
% 2.26/0.70  fof(f67,plain,(
% 2.26/0.70    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.26/0.70    inference(nnf_transformation,[],[f4])).
% 2.26/0.70  fof(f4,axiom,(
% 2.26/0.70    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.26/0.70  fof(f100,plain,(
% 2.26/0.70    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.26/0.70    inference(cnf_transformation,[],[f5])).
% 2.26/0.70  fof(f5,axiom,(
% 2.26/0.70    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 2.26/0.70  fof(f177,plain,(
% 2.26/0.70    r2_hidden(sK6(k1_xboole_0),k1_xboole_0) | sP0(k1_xboole_0)),
% 2.26/0.70    inference(superposition,[],[f94,f171])).
% 2.26/0.70  fof(f171,plain,(
% 2.26/0.70    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.26/0.70    inference(resolution,[],[f145,f78])).
% 2.26/0.70  fof(f78,plain,(
% 2.26/0.70    v1_xboole_0(k1_xboole_0)),
% 2.26/0.70    inference(cnf_transformation,[],[f1])).
% 2.26/0.70  fof(f1,axiom,(
% 2.26/0.70    v1_xboole_0(k1_xboole_0)),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.26/0.70  fof(f145,plain,(
% 2.26/0.70    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 2.26/0.70    inference(resolution,[],[f90,f89])).
% 2.26/0.70  fof(f89,plain,(
% 2.26/0.70    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.26/0.70    inference(cnf_transformation,[],[f32])).
% 2.26/0.70  fof(f32,plain,(
% 2.26/0.70    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.26/0.70    inference(ennf_transformation,[],[f2])).
% 2.26/0.70  fof(f2,axiom,(
% 2.26/0.70    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.26/0.70  fof(f90,plain,(
% 2.26/0.70    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.26/0.70    inference(cnf_transformation,[],[f33])).
% 2.26/0.70  fof(f33,plain,(
% 2.26/0.70    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 2.26/0.70    inference(ennf_transformation,[],[f10])).
% 2.26/0.70  fof(f10,axiom,(
% 2.26/0.70    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 2.26/0.70  fof(f94,plain,(
% 2.26/0.70    ( ! [X0] : (r2_hidden(sK6(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 2.26/0.70    inference(cnf_transformation,[],[f62])).
% 2.26/0.70  fof(f62,plain,(
% 2.26/0.70    ! [X0] : ((sP0(X0) | (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 2.26/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f60,f61])).
% 2.26/0.70  fof(f61,plain,(
% 2.26/0.70    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK6(X0) != sK7(X0) & k1_funct_1(X0,sK6(X0)) = k1_funct_1(X0,sK7(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)) & r2_hidden(sK6(X0),k1_relat_1(X0))))),
% 2.26/0.70    introduced(choice_axiom,[])).
% 2.26/0.70  fof(f60,plain,(
% 2.26/0.70    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 2.26/0.70    inference(rectify,[],[f59])).
% 2.26/0.70  fof(f59,plain,(
% 2.26/0.70    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 2.26/0.70    inference(nnf_transformation,[],[f52])).
% 2.26/0.70  fof(f52,plain,(
% 2.26/0.70    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 2.26/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.26/0.70  fof(f1383,plain,(
% 2.26/0.70    ~sP0(k1_xboole_0) | (spl8_1 | ~spl8_4 | ~spl8_10)),
% 2.26/0.70    inference(backward_demodulation,[],[f196,f1321])).
% 2.26/0.70  fof(f1321,plain,(
% 2.26/0.70    k1_xboole_0 = sK4 | ~spl8_10),
% 2.26/0.70    inference(resolution,[],[f254,f89])).
% 2.26/0.70  fof(f254,plain,(
% 2.26/0.70    v1_xboole_0(sK4) | ~spl8_10),
% 2.26/0.70    inference(avatar_component_clause,[],[f252])).
% 2.26/0.70  fof(f252,plain,(
% 2.26/0.70    spl8_10 <=> v1_xboole_0(sK4)),
% 2.26/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.26/0.70  fof(f196,plain,(
% 2.26/0.70    ~sP0(sK4) | (spl8_1 | ~spl8_4)),
% 2.26/0.70    inference(subsumption_resolution,[],[f194,f138])).
% 2.26/0.70  fof(f138,plain,(
% 2.26/0.70    ~v2_funct_1(sK4) | spl8_1),
% 2.26/0.70    inference(avatar_component_clause,[],[f136])).
% 2.26/0.70  fof(f194,plain,(
% 2.26/0.70    ~sP0(sK4) | v2_funct_1(sK4) | ~spl8_4),
% 2.26/0.70    inference(resolution,[],[f160,f92])).
% 2.26/0.70  fof(f92,plain,(
% 2.26/0.70    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 2.26/0.70    inference(cnf_transformation,[],[f58])).
% 2.26/0.70  fof(f58,plain,(
% 2.26/0.70    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 2.26/0.70    inference(nnf_transformation,[],[f53])).
% 2.26/0.70  fof(f53,plain,(
% 2.26/0.70    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 2.26/0.70    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.26/0.70  fof(f160,plain,(
% 2.26/0.70    sP1(sK4) | ~spl8_4),
% 2.26/0.70    inference(avatar_component_clause,[],[f158])).
% 2.26/0.70  fof(f158,plain,(
% 2.26/0.70    spl8_4 <=> sP1(sK4)),
% 2.26/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.26/0.70  fof(f1307,plain,(
% 2.26/0.70    spl8_9 | ~spl8_73),
% 2.26/0.70    inference(avatar_contradiction_clause,[],[f1306])).
% 2.26/0.70  fof(f1306,plain,(
% 2.26/0.70    $false | (spl8_9 | ~spl8_73)),
% 2.26/0.70    inference(subsumption_resolution,[],[f1282,f78])).
% 2.26/0.70  fof(f1282,plain,(
% 2.26/0.70    ~v1_xboole_0(k1_xboole_0) | (spl8_9 | ~spl8_73)),
% 2.26/0.70    inference(backward_demodulation,[],[f250,f1210])).
% 2.26/0.70  fof(f1210,plain,(
% 2.26/0.70    k1_xboole_0 = sK2 | ~spl8_73),
% 2.26/0.70    inference(avatar_component_clause,[],[f1208])).
% 2.26/0.70  fof(f250,plain,(
% 2.26/0.70    ~v1_xboole_0(sK2) | spl8_9),
% 2.26/0.70    inference(avatar_component_clause,[],[f248])).
% 2.26/0.70  fof(f248,plain,(
% 2.26/0.70    spl8_9 <=> v1_xboole_0(sK2)),
% 2.26/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.26/0.70  fof(f1256,plain,(
% 2.26/0.70    ~spl8_75 | spl8_76 | ~spl8_3 | ~spl8_5),
% 2.26/0.70    inference(avatar_split_clause,[],[f1247,f163,f154,f1253,f1249])).
% 2.26/0.70  fof(f154,plain,(
% 2.26/0.70    spl8_3 <=> v1_relat_1(sK4)),
% 2.26/0.70    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.26/0.70  fof(f1247,plain,(
% 2.26/0.70    sK2 = k2_relat_1(sK5) | ~r1_tarski(k2_relat_1(sK5),sK2) | (~spl8_3 | ~spl8_5)),
% 2.26/0.70    inference(forward_demodulation,[],[f1246,f125])).
% 2.26/0.70  fof(f125,plain,(
% 2.26/0.70    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.26/0.70    inference(definition_unfolding,[],[f86,f80])).
% 2.26/0.70  fof(f80,plain,(
% 2.26/0.70    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.26/0.70    inference(cnf_transformation,[],[f24])).
% 2.26/0.70  fof(f24,axiom,(
% 2.26/0.70    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.26/0.70  fof(f86,plain,(
% 2.26/0.70    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.26/0.70    inference(cnf_transformation,[],[f13])).
% 2.26/0.70  fof(f13,axiom,(
% 2.26/0.70    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.26/0.70  fof(f1246,plain,(
% 2.26/0.70    ~r1_tarski(k2_relat_1(sK5),sK2) | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2)) | (~spl8_3 | ~spl8_5)),
% 2.26/0.70    inference(forward_demodulation,[],[f1245,f125])).
% 2.26/0.70  fof(f1245,plain,(
% 2.26/0.70    ~r1_tarski(k2_relat_1(sK5),k2_relat_1(k6_partfun1(sK2))) | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2)) | (~spl8_3 | ~spl8_5)),
% 2.26/0.70    inference(subsumption_resolution,[],[f1244,f164])).
% 2.26/0.70  fof(f1244,plain,(
% 2.26/0.70    ~r1_tarski(k2_relat_1(sK5),k2_relat_1(k6_partfun1(sK2))) | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2)) | ~v1_relat_1(sK5) | ~spl8_3),
% 2.26/0.70    inference(subsumption_resolution,[],[f1239,f155])).
% 2.26/0.70  fof(f155,plain,(
% 2.26/0.70    v1_relat_1(sK4) | ~spl8_3),
% 2.26/0.70    inference(avatar_component_clause,[],[f154])).
% 2.26/0.70  fof(f1239,plain,(
% 2.26/0.70    ~r1_tarski(k2_relat_1(sK5),k2_relat_1(k6_partfun1(sK2))) | ~v1_relat_1(sK4) | k2_relat_1(sK5) = k2_relat_1(k6_partfun1(sK2)) | ~v1_relat_1(sK5)),
% 2.26/0.70    inference(superposition,[],[f324,f1217])).
% 2.26/0.70  fof(f1217,plain,(
% 2.26/0.70    k6_partfun1(sK2) = k5_relat_1(sK4,sK5)),
% 2.26/0.70    inference(global_subsumption,[],[f1195,f1216])).
% 2.26/0.70  fof(f1216,plain,(
% 2.26/0.70    k6_partfun1(sK2) = k5_relat_1(sK4,sK5) | ~m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.26/0.70    inference(resolution,[],[f1183,f382])).
% 2.26/0.70  fof(f382,plain,(
% 2.26/0.70    ( ! [X4,X3] : (~r2_relset_1(X3,X3,X4,k6_partfun1(X3)) | k6_partfun1(X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 2.26/0.70    inference(resolution,[],[f118,f84])).
% 2.26/0.70  fof(f84,plain,(
% 2.26/0.70    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.26/0.70    inference(cnf_transformation,[],[f22])).
% 2.26/0.70  fof(f22,axiom,(
% 2.26/0.70    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.26/0.70  fof(f118,plain,(
% 2.26/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.70    inference(cnf_transformation,[],[f69])).
% 2.26/0.70  fof(f69,plain,(
% 2.26/0.70    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.70    inference(nnf_transformation,[],[f47])).
% 2.26/0.70  fof(f47,plain,(
% 2.26/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.70    inference(flattening,[],[f46])).
% 2.26/0.70  fof(f46,plain,(
% 2.26/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.26/0.70    inference(ennf_transformation,[],[f19])).
% 2.26/0.70  fof(f19,axiom,(
% 2.26/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.26/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.26/0.70  fof(f1183,plain,(
% 2.26/0.70    r2_relset_1(sK2,sK2,k5_relat_1(sK4,sK5),k6_partfun1(sK2))),
% 2.26/0.70    inference(backward_demodulation,[],[f76,f856])).
% 2.26/0.70  fof(f76,plain,(
% 2.26/0.70    r2_relset_1(sK2,sK2,k1_partfun1(sK2,sK3,sK3,sK2,sK4,sK5),k6_partfun1(sK2))),
% 2.26/0.70    inference(cnf_transformation,[],[f57])).
% 2.26/0.70  fof(f1195,plain,(
% 2.26/0.70    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 2.26/0.70    inference(subsumption_resolution,[],[f1194,f70])).
% 2.26/0.70  fof(f1194,plain,(
% 2.26/0.70    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK4)),
% 2.26/0.70    inference(subsumption_resolution,[],[f1193,f72])).
% 2.26/0.70  fof(f1193,plain,(
% 2.26/0.70    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(sK4)),
% 2.26/0.70    inference(subsumption_resolution,[],[f1192,f73])).
% 2.26/0.70  fof(f1192,plain,(
% 2.26/0.70    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(sK4)),
% 2.26/0.70    inference(subsumption_resolution,[],[f1185,f75])).
% 2.26/0.70  fof(f1185,plain,(
% 2.26/0.70    m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_1(sK4)),
% 2.26/0.70    inference(superposition,[],[f122,f856])).
% 2.26/0.70  fof(f122,plain,(
% 2.26/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.26/0.70    inference(cnf_transformation,[],[f51])).
% 2.26/0.70  fof(f51,plain,(
% 2.26/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.26/0.70    inference(flattening,[],[f50])).
% 2.26/0.71  fof(f50,plain,(
% 2.26/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.26/0.71    inference(ennf_transformation,[],[f21])).
% 2.26/0.71  fof(f21,axiom,(
% 2.26/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.26/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.26/0.71  fof(f324,plain,(
% 2.26/0.71    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 2.26/0.71    inference(resolution,[],[f87,f109])).
% 2.26/0.71  fof(f109,plain,(
% 2.26/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.26/0.71    inference(cnf_transformation,[],[f66])).
% 2.26/0.71  fof(f87,plain,(
% 2.26/0.71    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.26/0.71    inference(cnf_transformation,[],[f30])).
% 2.26/0.71  fof(f30,plain,(
% 2.26/0.71    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.26/0.71    inference(ennf_transformation,[],[f12])).
% 2.26/0.71  fof(f12,axiom,(
% 2.26/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.26/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 2.26/0.71  fof(f1243,plain,(
% 2.26/0.71    spl8_74),
% 2.26/0.71    inference(avatar_contradiction_clause,[],[f1242])).
% 2.26/0.71  fof(f1242,plain,(
% 2.26/0.71    $false | spl8_74),
% 2.26/0.71    inference(subsumption_resolution,[],[f1236,f123])).
% 2.26/0.71  fof(f123,plain,(
% 2.26/0.71    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.26/0.71    inference(definition_unfolding,[],[f82,f80])).
% 2.26/0.71  fof(f82,plain,(
% 2.26/0.71    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.26/0.71    inference(cnf_transformation,[],[f15])).
% 2.26/0.71  fof(f15,axiom,(
% 2.26/0.71    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.26/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.26/0.71  fof(f1236,plain,(
% 2.26/0.71    ~v2_funct_1(k6_partfun1(sK2)) | spl8_74),
% 2.26/0.71    inference(backward_demodulation,[],[f1214,f1217])).
% 2.26/0.71  fof(f1214,plain,(
% 2.26/0.71    ~v2_funct_1(k5_relat_1(sK4,sK5)) | spl8_74),
% 2.26/0.71    inference(avatar_component_clause,[],[f1212])).
% 2.26/0.71  fof(f255,plain,(
% 2.26/0.71    ~spl8_9 | spl8_10),
% 2.26/0.71    inference(avatar_split_clause,[],[f243,f252,f248])).
% 2.26/0.71  fof(f243,plain,(
% 2.26/0.71    v1_xboole_0(sK4) | ~v1_xboole_0(sK2)),
% 2.26/0.71    inference(resolution,[],[f103,f72])).
% 2.26/0.71  fof(f103,plain,(
% 2.26/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 2.26/0.71    inference(cnf_transformation,[],[f37])).
% 2.26/0.71  fof(f37,plain,(
% 2.26/0.71    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.26/0.71    inference(ennf_transformation,[],[f17])).
% 2.26/0.71  fof(f17,axiom,(
% 2.26/0.71    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.26/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 2.26/0.71  fof(f191,plain,(
% 2.26/0.71    spl8_5),
% 2.26/0.71    inference(avatar_contradiction_clause,[],[f190])).
% 2.26/0.71  fof(f190,plain,(
% 2.26/0.71    $false | spl8_5),
% 2.26/0.71    inference(subsumption_resolution,[],[f189,f99])).
% 2.26/0.71  fof(f99,plain,(
% 2.26/0.71    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.26/0.71    inference(cnf_transformation,[],[f11])).
% 2.26/0.71  fof(f11,axiom,(
% 2.26/0.71    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.26/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.26/0.71  fof(f189,plain,(
% 2.26/0.71    ~v1_relat_1(k2_zfmisc_1(sK3,sK2)) | spl8_5),
% 2.26/0.71    inference(subsumption_resolution,[],[f185,f165])).
% 2.26/0.71  fof(f165,plain,(
% 2.26/0.71    ~v1_relat_1(sK5) | spl8_5),
% 2.26/0.71    inference(avatar_component_clause,[],[f163])).
% 2.26/0.71  fof(f185,plain,(
% 2.26/0.71    v1_relat_1(sK5) | ~v1_relat_1(k2_zfmisc_1(sK3,sK2))),
% 2.26/0.71    inference(resolution,[],[f88,f75])).
% 2.26/0.71  fof(f88,plain,(
% 2.26/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.26/0.71    inference(cnf_transformation,[],[f31])).
% 2.26/0.71  fof(f31,plain,(
% 2.26/0.71    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.26/0.71    inference(ennf_transformation,[],[f8])).
% 2.26/0.71  fof(f8,axiom,(
% 2.26/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.26/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.26/0.71  fof(f188,plain,(
% 2.26/0.71    spl8_3),
% 2.26/0.71    inference(avatar_contradiction_clause,[],[f187])).
% 2.26/0.71  fof(f187,plain,(
% 2.26/0.71    $false | spl8_3),
% 2.26/0.71    inference(subsumption_resolution,[],[f186,f99])).
% 2.26/0.71  fof(f186,plain,(
% 2.26/0.71    ~v1_relat_1(k2_zfmisc_1(sK2,sK3)) | spl8_3),
% 2.26/0.71    inference(subsumption_resolution,[],[f184,f156])).
% 2.26/0.71  fof(f156,plain,(
% 2.26/0.71    ~v1_relat_1(sK4) | spl8_3),
% 2.26/0.71    inference(avatar_component_clause,[],[f154])).
% 2.26/0.71  fof(f184,plain,(
% 2.26/0.71    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK3))),
% 2.26/0.71    inference(resolution,[],[f88,f72])).
% 2.26/0.71  fof(f161,plain,(
% 2.26/0.71    ~spl8_3 | spl8_4),
% 2.26/0.71    inference(avatar_split_clause,[],[f151,f158,f154])).
% 2.26/0.71  fof(f151,plain,(
% 2.26/0.71    sP1(sK4) | ~v1_relat_1(sK4)),
% 2.26/0.71    inference(resolution,[],[f98,f70])).
% 2.26/0.71  fof(f98,plain,(
% 2.26/0.71    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 2.26/0.71    inference(cnf_transformation,[],[f54])).
% 2.26/0.71  fof(f54,plain,(
% 2.26/0.71    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.26/0.71    inference(definition_folding,[],[f35,f53,f52])).
% 2.26/0.71  fof(f35,plain,(
% 2.26/0.71    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.26/0.71    inference(flattening,[],[f34])).
% 2.26/0.71  fof(f34,plain,(
% 2.26/0.71    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.26/0.71    inference(ennf_transformation,[],[f14])).
% 2.26/0.71  fof(f14,axiom,(
% 2.26/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.26/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 2.26/0.71  fof(f143,plain,(
% 2.26/0.71    ~spl8_1 | ~spl8_2),
% 2.26/0.71    inference(avatar_split_clause,[],[f77,f140,f136])).
% 2.26/0.71  fof(f77,plain,(
% 2.26/0.71    ~v2_funct_2(sK5,sK2) | ~v2_funct_1(sK4)),
% 2.26/0.71    inference(cnf_transformation,[],[f57])).
% 2.26/0.71  % SZS output end Proof for theBenchmark
% 2.26/0.71  % (31389)------------------------------
% 2.26/0.71  % (31389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.71  % (31389)Termination reason: Refutation
% 2.26/0.71  
% 2.26/0.71  % (31389)Memory used [KB]: 11769
% 2.26/0.71  % (31389)Time elapsed: 0.261 s
% 2.26/0.71  % (31389)------------------------------
% 2.26/0.71  % (31389)------------------------------
% 2.62/0.71  % (31377)Success in time 0.349 s
%------------------------------------------------------------------------------
