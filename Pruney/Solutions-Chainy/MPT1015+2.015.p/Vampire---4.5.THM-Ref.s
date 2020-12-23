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
% DateTime   : Thu Dec  3 13:05:27 EST 2020

% Result     : Theorem 5.08s
% Output     : Refutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :  281 ( 646 expanded)
%              Number of leaves         :   61 ( 250 expanded)
%              Depth                    :   11
%              Number of atoms          : 1037 (2572 expanded)
%              Number of equality atoms :  157 ( 310 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9378,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f147,f151,f460,f473,f475,f477,f479,f481,f493,f505,f510,f556,f570,f610,f627,f630,f643,f692,f778,f1321,f1342,f1395,f1503,f2064,f2099,f2136,f4140,f5249,f5274,f5286,f5376,f5431,f5496,f5513,f5534,f5544,f5565,f8777,f9377])).

fof(f9377,plain,(
    ~ spl3_51 ),
    inference(avatar_contradiction_clause,[],[f9372])).

fof(f9372,plain,
    ( $false
    | ~ spl3_51 ),
    inference(subsumption_resolution,[],[f255,f8915])).

fof(f8915,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_51 ),
    inference(superposition,[],[f73,f739])).

fof(f739,plain,
    ( sK2 = k6_partfun1(sK0)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f737])).

fof(f737,plain,
    ( spl3_51
  <=> sK2 = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f73,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f255,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f127,f70])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f8777,plain,
    ( spl3_504
    | ~ spl3_520
    | ~ spl3_521 ),
    inference(avatar_contradiction_clause,[],[f8743])).

fof(f8743,plain,
    ( $false
    | spl3_504
    | ~ spl3_520
    | ~ spl3_521 ),
    inference(subsumption_resolution,[],[f5426,f8742])).

fof(f8742,plain,
    ( k6_partfun1(sK0) = k2_funct_1(sK2)
    | ~ spl3_520
    | ~ spl3_521 ),
    inference(forward_demodulation,[],[f5529,f5532])).

fof(f5532,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_521 ),
    inference(avatar_component_clause,[],[f5531])).

fof(f5531,plain,
    ( spl3_521
  <=> sK0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_521])])).

fof(f5529,plain,
    ( k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | ~ spl3_520 ),
    inference(avatar_component_clause,[],[f5527])).

fof(f5527,plain,
    ( spl3_520
  <=> k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_520])])).

fof(f5426,plain,
    ( k6_partfun1(sK0) != k2_funct_1(sK2)
    | spl3_504 ),
    inference(avatar_component_clause,[],[f5424])).

fof(f5424,plain,
    ( spl3_504
  <=> k6_partfun1(sK0) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_504])])).

fof(f5565,plain,
    ( ~ spl3_1
    | ~ spl3_25
    | ~ spl3_12
    | ~ spl3_483
    | spl3_521 ),
    inference(avatar_split_clause,[],[f5564,f5531,f5264,f453,f545,f135])).

fof(f135,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f545,plain,
    ( spl3_25
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f453,plain,
    ( spl3_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f5264,plain,
    ( spl3_483
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_483])])).

fof(f5564,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_483
    | spl3_521 ),
    inference(trivial_inequality_removal,[],[f5563])).

fof(f5563,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_483
    | spl3_521 ),
    inference(forward_demodulation,[],[f5562,f5265])).

fof(f5265,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_483 ),
    inference(avatar_component_clause,[],[f5264])).

fof(f5562,plain,
    ( sK0 != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_521 ),
    inference(superposition,[],[f5533,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f5533,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK2))
    | spl3_521 ),
    inference(avatar_component_clause,[],[f5531])).

fof(f5544,plain,
    ( ~ spl3_27
    | ~ spl3_26
    | spl3_505
    | ~ spl3_519 ),
    inference(avatar_split_clause,[],[f5539,f5493,f5428,f549,f553])).

fof(f553,plain,
    ( spl3_27
  <=> v5_relat_1(k2_funct_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f549,plain,
    ( spl3_26
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f5428,plain,
    ( spl3_505
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_505])])).

fof(f5493,plain,
    ( spl3_519
  <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_519])])).

fof(f5539,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ spl3_519 ),
    inference(resolution,[],[f5495,f170])).

fof(f170,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k2_relat_1(X3))
      | k2_relat_1(X3) = X2
      | ~ v1_relat_1(X3)
      | ~ v5_relat_1(X3,X2) ) ),
    inference(resolution,[],[f104,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5495,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_519 ),
    inference(avatar_component_clause,[],[f5493])).

fof(f5534,plain,
    ( ~ spl3_1
    | ~ spl3_34
    | ~ spl3_25
    | ~ spl3_15
    | ~ spl3_3
    | ~ spl3_12
    | spl3_520
    | ~ spl3_35
    | ~ spl3_503
    | ~ spl3_26
    | ~ spl3_75
    | ~ spl3_521
    | ~ spl3_59
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f5525,f1339,f1147,f5531,f1397,f549,f5420,f603,f5527,f453,f144,f466,f545,f599,f135])).

fof(f599,plain,
    ( spl3_34
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f466,plain,
    ( spl3_15
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f144,plain,
    ( spl3_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f603,plain,
    ( spl3_35
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f5420,plain,
    ( spl3_503
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_503])])).

fof(f1397,plain,
    ( spl3_75
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f1147,plain,
    ( spl3_59
  <=> sK1 = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f1339,plain,
    ( spl3_71
  <=> sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f5525,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_59
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f5522,f1341])).

fof(f1341,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f1339])).

fof(f5522,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_59 ),
    inference(trivial_inequality_removal,[],[f5517])).

fof(f5517,plain,
    ( k2_funct_1(sK1) != k2_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_59 ),
    inference(superposition,[],[f854,f1149])).

fof(f1149,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f854,plain,(
    ! [X2,X1] :
      ( k2_funct_1(X1) != k2_funct_1(k5_relat_1(X2,X1))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v1_funct_1(k2_funct_1(X2))
      | k2_relat_1(k2_funct_1(X1)) != k1_relat_1(k2_funct_1(X2))
      | ~ v1_relat_1(k2_funct_1(X1))
      | k2_funct_1(X2) = k6_partfun1(k1_relat_1(k2_funct_1(X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X2)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f123,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(f123,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(definition_unfolding,[],[f94,f77])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f5513,plain,
    ( ~ spl3_1
    | spl3_503 ),
    inference(avatar_contradiction_clause,[],[f5510])).

fof(f5510,plain,
    ( $false
    | ~ spl3_1
    | spl3_503 ),
    inference(unit_resulting_resolution,[],[f137,f68,f5422,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f5422,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_503 ),
    inference(avatar_component_clause,[],[f5420])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f137,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f5496,plain,
    ( ~ spl3_1
    | ~ spl3_25
    | ~ spl3_12
    | ~ spl3_26
    | spl3_519
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f1312,f489,f5493,f549,f453,f545,f135])).

fof(f489,plain,
    ( spl3_18
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f1312,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(superposition,[],[f1240,f491])).

fof(f491,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f489])).

fof(f1240,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f1231])).

fof(f1231,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k2_funct_1(X1))
      | r1_tarski(k1_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X1)) ) ),
    inference(resolution,[],[f302,f160])).

fof(f160,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f97,f124])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f302,plain,(
    ! [X6,X5] :
      ( ~ v5_relat_1(k2_funct_1(X5),X6)
      | ~ v1_relat_1(k2_funct_1(X5))
      | r1_tarski(k1_relat_1(X5),X6)
      | ~ v1_funct_1(X5)
      | ~ v2_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f98,f88])).

fof(f88,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5431,plain,
    ( ~ spl3_25
    | ~ spl3_26
    | ~ spl3_12
    | ~ spl3_1
    | ~ spl3_503
    | ~ spl3_504
    | ~ spl3_505
    | spl3_51
    | ~ spl3_18
    | ~ spl3_483 ),
    inference(avatar_split_clause,[],[f5418,f5264,f489,f737,f5428,f5424,f5420,f135,f453,f549,f545])).

fof(f5418,plain,
    ( sK2 = k6_partfun1(sK0)
    | sK0 != k2_relat_1(k2_funct_1(sK2))
    | k6_partfun1(sK0) != k2_funct_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_18
    | ~ spl3_483 ),
    inference(forward_demodulation,[],[f5417,f491])).

fof(f5417,plain,
    ( sK0 != k2_relat_1(k2_funct_1(sK2))
    | k6_partfun1(sK0) != k2_funct_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | sK2 = k6_partfun1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_18
    | ~ spl3_483 ),
    inference(forward_demodulation,[],[f5325,f491])).

fof(f5325,plain,
    ( k6_partfun1(sK0) != k2_funct_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | sK2 = k6_partfun1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_483 ),
    inference(superposition,[],[f857,f5265])).

fof(f857,plain,(
    ! [X0] :
      ( k2_funct_1(X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | k6_partfun1(k1_relat_1(X0)) = X0
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f853])).

fof(f853,plain,(
    ! [X0] :
      ( k2_funct_1(X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | k6_partfun1(k1_relat_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f123,f121])).

fof(f121,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f90,f77])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f5376,plain,
    ( ~ spl3_1
    | ~ spl3_12
    | spl3_25
    | ~ spl3_34
    | ~ spl3_39
    | ~ spl3_59
    | ~ spl3_483 ),
    inference(avatar_split_clause,[],[f5375,f5264,f1147,f641,f599,f545,f453,f135])).

fof(f641,plain,
    ( spl3_39
  <=> ! [X4] :
        ( sK0 != k2_relat_1(X4)
        | v2_funct_1(X4)
        | ~ v2_funct_1(k5_relat_1(X4,sK1))
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f5375,plain,
    ( ~ v2_funct_1(sK1)
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_39
    | ~ spl3_59
    | ~ spl3_483 ),
    inference(forward_demodulation,[],[f5337,f1149])).

fof(f5337,plain,
    ( v2_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_39
    | ~ spl3_483 ),
    inference(trivial_inequality_removal,[],[f5317])).

fof(f5317,plain,
    ( sK0 != sK0
    | v2_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_39
    | ~ spl3_483 ),
    inference(superposition,[],[f642,f5265])).

fof(f642,plain,
    ( ! [X4] :
        ( sK0 != k2_relat_1(X4)
        | v2_funct_1(X4)
        | ~ v2_funct_1(k5_relat_1(X4,sK1))
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(X4) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f641])).

fof(f5286,plain,
    ( ~ spl3_1
    | spl3_484 ),
    inference(avatar_contradiction_clause,[],[f5284])).

fof(f5284,plain,
    ( $false
    | ~ spl3_1
    | spl3_484 ),
    inference(unit_resulting_resolution,[],[f137,f194,f5273,f98])).

fof(f5273,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_484 ),
    inference(avatar_component_clause,[],[f5271])).

fof(f5271,plain,
    ( spl3_484
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_484])])).

fof(f194,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f110,f70])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f5274,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_34
    | ~ spl3_15
    | spl3_483
    | ~ spl3_484
    | ~ spl3_20
    | ~ spl3_59
    | ~ spl3_130 ),
    inference(avatar_split_clause,[],[f5269,f2092,f1147,f501,f5271,f5264,f466,f599,f144,f135])).

fof(f501,plain,
    ( spl3_20
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f2092,plain,
    ( spl3_130
  <=> sK0 = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).

fof(f5269,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | sK0 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_20
    | ~ spl3_59
    | ~ spl3_130 ),
    inference(forward_demodulation,[],[f5268,f503])).

fof(f503,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f501])).

fof(f5268,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_59
    | ~ spl3_130 ),
    inference(forward_demodulation,[],[f5257,f2094])).

fof(f2094,plain,
    ( sK0 = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl3_130 ),
    inference(avatar_component_clause,[],[f2092])).

fof(f5257,plain,
    ( k2_relat_1(sK2) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_59 ),
    inference(superposition,[],[f413,f1149])).

fof(f413,plain,(
    ! [X2,X3] :
      ( k2_relat_1(X3) = k10_relat_1(X2,k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,(
    ! [X2,X3] :
      ( k2_relat_1(X3) = k10_relat_1(X2,k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X2))
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f99,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f5249,plain,
    ( ~ spl3_12
    | ~ spl3_19
    | ~ spl3_15
    | ~ spl3_17
    | spl3_59
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f5240,f775,f1147,f485,f466,f497,f453])).

fof(f497,plain,
    ( spl3_19
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f485,plain,
    ( spl3_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f775,plain,
    ( spl3_56
  <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f5240,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_56 ),
    inference(superposition,[],[f116,f777])).

fof(f777,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f775])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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

fof(f4140,plain,(
    spl3_55 ),
    inference(avatar_contradiction_clause,[],[f4128])).

fof(f4128,plain,
    ( $false
    | spl3_55 ),
    inference(unit_resulting_resolution,[],[f74,f68,f70,f76,f773,f1196])).

fof(f1196,plain,(
    ! [X57,X54,X52,X56,X55,X53] :
      ( r1_tarski(k1_partfun1(X53,X54,X56,X57,X52,X55),k2_zfmisc_1(X53,X57))
      | ~ v1_funct_1(X55)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | ~ v1_funct_1(X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ),
    inference(resolution,[],[f118,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f773,plain,
    ( ~ r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k2_zfmisc_1(sK0,sK0))
    | spl3_55 ),
    inference(avatar_component_clause,[],[f771])).

fof(f771,plain,
    ( spl3_55
  <=> r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f2136,plain,(
    spl3_131 ),
    inference(avatar_contradiction_clause,[],[f2132])).

fof(f2132,plain,
    ( $false
    | spl3_131 ),
    inference(unit_resulting_resolution,[],[f124,f2098])).

fof(f2098,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_131 ),
    inference(avatar_component_clause,[],[f2096])).

fof(f2096,plain,
    ( spl3_131
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).

fof(f2099,plain,
    ( ~ spl3_3
    | ~ spl3_34
    | ~ spl3_15
    | spl3_130
    | ~ spl3_131
    | ~ spl3_20
    | ~ spl3_128 ),
    inference(avatar_split_clause,[],[f2090,f2061,f501,f2096,f2092,f466,f599,f144])).

fof(f2061,plain,
    ( spl3_128
  <=> k2_relat_1(sK1) = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).

fof(f2090,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_20
    | ~ spl3_128 ),
    inference(forward_demodulation,[],[f2075,f503])).

fof(f2075,plain,
    ( sK0 = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_128 ),
    inference(superposition,[],[f99,f2063])).

fof(f2063,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,sK0)
    | ~ spl3_128 ),
    inference(avatar_component_clause,[],[f2061])).

fof(f2064,plain,
    ( ~ spl3_34
    | ~ spl3_15
    | ~ spl3_3
    | spl3_128
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f2059,f1393,f2061,f144,f466,f599])).

fof(f1393,plain,
    ( spl3_74
  <=> ! [X0] :
        ( k2_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(X0,sK0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f2059,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f2058,f119])).

fof(f119,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f79,f77])).

fof(f79,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f2058,plain,
    ( k2_relat_1(k6_partfun1(k2_relat_1(sK1))) = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ spl3_74 ),
    inference(duplicate_literal_removal,[],[f2010])).

fof(f2010,plain,
    ( k2_relat_1(k6_partfun1(k2_relat_1(sK1))) = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_74 ),
    inference(superposition,[],[f1394,f121])).

fof(f1394,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(X0,sK0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f1393])).

fof(f1503,plain,
    ( ~ spl3_3
    | spl3_75 ),
    inference(avatar_contradiction_clause,[],[f1501])).

fof(f1501,plain,
    ( $false
    | ~ spl3_3
    | spl3_75 ),
    inference(unit_resulting_resolution,[],[f146,f74,f1399,f86])).

fof(f1399,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl3_75 ),
    inference(avatar_component_clause,[],[f1397])).

fof(f146,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f1395,plain,
    ( ~ spl3_35
    | spl3_74
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f1356,f1339,f1393,f603])).

fof(f1356,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(X0,sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK1)) )
    | ~ spl3_71 ),
    inference(superposition,[],[f81,f1341])).

fof(f1342,plain,
    ( ~ spl3_36
    | ~ spl3_35
    | spl3_71
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f1333,f1318,f1339,f603,f607])).

fof(f607,plain,
    ( spl3_36
  <=> v5_relat_1(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f1318,plain,
    ( spl3_70
  <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f1333,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl3_70 ),
    inference(resolution,[],[f1320,f170])).

fof(f1320,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1321,plain,
    ( ~ spl3_3
    | ~ spl3_34
    | ~ spl3_15
    | ~ spl3_35
    | spl3_70
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f1311,f501,f1318,f603,f466,f599,f144])).

fof(f1311,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_20 ),
    inference(superposition,[],[f1240,f503])).

fof(f778,plain,
    ( ~ spl3_55
    | spl3_56 ),
    inference(avatar_split_clause,[],[f768,f775,f771])).

fof(f768,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k2_zfmisc_1(sK0,sK0)) ),
    inference(resolution,[],[f753,f71])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f753,plain,(
    ! [X0] :
      ( ~ r2_relset_1(sK0,sK0,X0,sK1)
      | sK1 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(sK0,sK0)) ) ),
    inference(resolution,[],[f695,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f695,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | sK1 = X1
      | ~ r2_relset_1(sK0,sK0,X1,sK1) ) ),
    inference(resolution,[],[f115,f76])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f692,plain,
    ( ~ spl3_1
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f690])).

fof(f690,plain,
    ( $false
    | ~ spl3_1
    | spl3_26 ),
    inference(unit_resulting_resolution,[],[f137,f68,f551,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f551,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f549])).

fof(f643,plain,
    ( ~ spl3_3
    | ~ spl3_15
    | spl3_39
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f638,f501,f641,f466,f144])).

fof(f638,plain,
    ( ! [X4] :
        ( sK0 != k2_relat_1(X4)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v2_funct_1(k5_relat_1(X4,sK1))
        | ~ v1_relat_1(sK1)
        | v2_funct_1(X4) )
    | ~ spl3_20 ),
    inference(superposition,[],[f92,f503])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f630,plain,
    ( ~ spl3_3
    | spl3_35 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl3_3
    | spl3_35 ),
    inference(unit_resulting_resolution,[],[f146,f74,f605,f85])).

fof(f605,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f603])).

fof(f627,plain,(
    spl3_34 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | spl3_34 ),
    inference(subsumption_resolution,[],[f72,f601])).

fof(f601,plain,
    ( ~ v2_funct_1(sK1)
    | spl3_34 ),
    inference(avatar_component_clause,[],[f599])).

fof(f72,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f610,plain,
    ( ~ spl3_3
    | ~ spl3_34
    | ~ spl3_15
    | ~ spl3_35
    | spl3_36
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f576,f501,f607,f603,f466,f599,f144])).

fof(f576,plain,
    ( v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_20 ),
    inference(superposition,[],[f303,f503])).

fof(f303,plain,(
    ! [X7] :
      ( v5_relat_1(k2_funct_1(X7),k1_relat_1(X7))
      | ~ v1_relat_1(k2_funct_1(X7))
      | ~ v1_funct_1(X7)
      | ~ v2_funct_1(X7)
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f160,f88])).

fof(f570,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl3_19 ),
    inference(subsumption_resolution,[],[f76,f499])).

fof(f499,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f497])).

fof(f556,plain,
    ( ~ spl3_1
    | ~ spl3_25
    | ~ spl3_12
    | ~ spl3_26
    | spl3_27
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f522,f489,f553,f549,f453,f545,f135])).

fof(f522,plain,
    ( v5_relat_1(k2_funct_1(sK2),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(superposition,[],[f303,f491])).

fof(f510,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | spl3_17 ),
    inference(subsumption_resolution,[],[f70,f487])).

fof(f487,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f485])).

fof(f505,plain,
    ( ~ spl3_19
    | spl3_20
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f495,f462,f501,f497])).

fof(f462,plain,
    ( spl3_14
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f495,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_14 ),
    inference(superposition,[],[f107,f464])).

fof(f464,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f462])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f493,plain,
    ( ~ spl3_17
    | spl3_18
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f483,f449,f489,f485])).

fof(f449,plain,
    ( spl3_11
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f483,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_11 ),
    inference(superposition,[],[f107,f451])).

fof(f451,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f449])).

fof(f481,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl3_15 ),
    inference(subsumption_resolution,[],[f74,f468])).

fof(f468,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f466])).

fof(f479,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | spl3_16 ),
    inference(subsumption_resolution,[],[f75,f472])).

fof(f472,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl3_16
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f75,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f477,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f69,f459])).

fof(f459,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f475,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f68,f455])).

fof(f455,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f453])).

fof(f473,plain,
    ( spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f444,f470,f466,f462])).

fof(f444,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f101,f76])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f460,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f443,f457,f453,f449])).

fof(f443,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f101,f70])).

fof(f151,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f95,f141])).

fof(f141,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_2
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f147,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f132,f139,f144])).

fof(f132,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(resolution,[],[f82,f76])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f142,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f131,f139,f135])).

fof(f131,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f82,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (27215)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.48  % (27208)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (27204)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.49  % (27203)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (27217)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.50  % (27225)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.50  % (27233)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (27205)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (27207)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (27227)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (27219)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (27220)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (27209)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27206)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (27216)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (27226)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (27229)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (27232)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (27230)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (27221)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (27222)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (27224)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (27231)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (27210)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (27212)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (27211)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (27214)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (27228)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (27223)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (27213)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (27220)Refutation not found, incomplete strategy% (27220)------------------------------
% 0.21/0.54  % (27220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27220)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27220)Memory used [KB]: 10746
% 0.21/0.54  % (27220)Time elapsed: 0.114 s
% 0.21/0.54  % (27220)------------------------------
% 0.21/0.54  % (27220)------------------------------
% 2.08/0.66  % (27330)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.39/0.83  % (27205)Time limit reached!
% 3.39/0.83  % (27205)------------------------------
% 3.39/0.83  % (27205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.83  % (27205)Termination reason: Time limit
% 3.39/0.83  
% 3.39/0.83  % (27205)Memory used [KB]: 6908
% 3.39/0.83  % (27205)Time elapsed: 0.421 s
% 3.39/0.83  % (27205)------------------------------
% 3.39/0.83  % (27205)------------------------------
% 3.39/0.83  % (27228)Time limit reached!
% 3.39/0.83  % (27228)------------------------------
% 3.39/0.83  % (27228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.83  % (27228)Termination reason: Time limit
% 3.39/0.83  
% 3.39/0.83  % (27228)Memory used [KB]: 13176
% 3.39/0.83  % (27228)Time elapsed: 0.412 s
% 3.39/0.83  % (27228)------------------------------
% 3.39/0.83  % (27228)------------------------------
% 4.24/0.91  % (27233)Time limit reached!
% 4.24/0.91  % (27233)------------------------------
% 4.24/0.91  % (27233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.91  % (27233)Termination reason: Time limit
% 4.24/0.91  % (27233)Termination phase: Saturation
% 4.24/0.91  
% 4.24/0.91  % (27233)Memory used [KB]: 5373
% 4.24/0.91  % (27233)Time elapsed: 0.500 s
% 4.24/0.91  % (27233)------------------------------
% 4.24/0.91  % (27233)------------------------------
% 4.24/0.92  % (27217)Time limit reached!
% 4.24/0.92  % (27217)------------------------------
% 4.24/0.92  % (27217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.92  % (27209)Time limit reached!
% 4.24/0.92  % (27209)------------------------------
% 4.24/0.92  % (27209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.24/0.92  % (27209)Termination reason: Time limit
% 4.24/0.92  
% 4.24/0.92  % (27209)Memory used [KB]: 15479
% 4.24/0.92  % (27209)Time elapsed: 0.521 s
% 4.24/0.92  % (27209)------------------------------
% 4.24/0.92  % (27209)------------------------------
% 4.42/0.93  % (27217)Termination reason: Time limit
% 4.42/0.93  
% 4.42/0.93  % (27217)Memory used [KB]: 7036
% 4.42/0.93  % (27217)Time elapsed: 0.517 s
% 4.42/0.93  % (27217)------------------------------
% 4.42/0.93  % (27217)------------------------------
% 4.42/0.95  % (27423)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.42/0.97  % (27422)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.42/1.02  % (27424)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.42/1.02  % (27210)Time limit reached!
% 4.42/1.02  % (27210)------------------------------
% 4.42/1.02  % (27210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/1.02  % (27210)Termination reason: Time limit
% 4.42/1.02  % (27210)Termination phase: Saturation
% 4.42/1.02  
% 4.42/1.02  % (27210)Memory used [KB]: 6524
% 4.42/1.02  % (27210)Time elapsed: 0.600 s
% 4.42/1.02  % (27210)------------------------------
% 4.42/1.02  % (27210)------------------------------
% 5.08/1.03  % (27425)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.08/1.03  % (27426)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.08/1.08  % (27216)Refutation found. Thanks to Tanya!
% 5.08/1.08  % SZS status Theorem for theBenchmark
% 5.08/1.08  % SZS output start Proof for theBenchmark
% 5.08/1.08  fof(f9378,plain,(
% 5.08/1.08    $false),
% 5.08/1.08    inference(avatar_sat_refutation,[],[f142,f147,f151,f460,f473,f475,f477,f479,f481,f493,f505,f510,f556,f570,f610,f627,f630,f643,f692,f778,f1321,f1342,f1395,f1503,f2064,f2099,f2136,f4140,f5249,f5274,f5286,f5376,f5431,f5496,f5513,f5534,f5544,f5565,f8777,f9377])).
% 5.08/1.08  fof(f9377,plain,(
% 5.08/1.08    ~spl3_51),
% 5.08/1.08    inference(avatar_contradiction_clause,[],[f9372])).
% 5.08/1.08  fof(f9372,plain,(
% 5.08/1.08    $false | ~spl3_51),
% 5.08/1.08    inference(subsumption_resolution,[],[f255,f8915])).
% 5.08/1.08  fof(f8915,plain,(
% 5.08/1.08    ~r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_51),
% 5.08/1.08    inference(superposition,[],[f73,f739])).
% 5.08/1.08  fof(f739,plain,(
% 5.08/1.08    sK2 = k6_partfun1(sK0) | ~spl3_51),
% 5.08/1.08    inference(avatar_component_clause,[],[f737])).
% 5.08/1.08  fof(f737,plain,(
% 5.08/1.08    spl3_51 <=> sK2 = k6_partfun1(sK0)),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 5.08/1.08  fof(f73,plain,(
% 5.08/1.08    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 5.08/1.08    inference(cnf_transformation,[],[f31])).
% 5.08/1.08  fof(f31,plain,(
% 5.08/1.08    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 5.08/1.08    inference(flattening,[],[f30])).
% 5.08/1.08  fof(f30,plain,(
% 5.08/1.08    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 5.08/1.08    inference(ennf_transformation,[],[f29])).
% 5.08/1.08  fof(f29,negated_conjecture,(
% 5.08/1.08    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 5.08/1.08    inference(negated_conjecture,[],[f28])).
% 5.08/1.08  fof(f28,conjecture,(
% 5.08/1.08    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 5.08/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 5.08/1.08  fof(f255,plain,(
% 5.08/1.08    r2_relset_1(sK0,sK0,sK2,sK2)),
% 5.08/1.08    inference(resolution,[],[f127,f70])).
% 5.08/1.08  fof(f70,plain,(
% 5.08/1.08    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 5.08/1.08    inference(cnf_transformation,[],[f31])).
% 5.08/1.08  fof(f127,plain,(
% 5.08/1.08    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 5.08/1.08    inference(duplicate_literal_removal,[],[f126])).
% 5.08/1.08  fof(f126,plain,(
% 5.08/1.08    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 5.08/1.08    inference(equality_resolution,[],[f114])).
% 5.08/1.08  fof(f114,plain,(
% 5.08/1.08    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 5.08/1.08    inference(cnf_transformation,[],[f63])).
% 5.08/1.08  fof(f63,plain,(
% 5.08/1.08    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.08/1.08    inference(flattening,[],[f62])).
% 5.08/1.08  fof(f62,plain,(
% 5.08/1.08    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 5.08/1.08    inference(ennf_transformation,[],[f21])).
% 5.08/1.08  fof(f21,axiom,(
% 5.08/1.08    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 5.08/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 5.08/1.08  fof(f8777,plain,(
% 5.08/1.08    spl3_504 | ~spl3_520 | ~spl3_521),
% 5.08/1.08    inference(avatar_contradiction_clause,[],[f8743])).
% 5.08/1.08  fof(f8743,plain,(
% 5.08/1.08    $false | (spl3_504 | ~spl3_520 | ~spl3_521)),
% 5.08/1.08    inference(subsumption_resolution,[],[f5426,f8742])).
% 5.08/1.08  fof(f8742,plain,(
% 5.08/1.08    k6_partfun1(sK0) = k2_funct_1(sK2) | (~spl3_520 | ~spl3_521)),
% 5.08/1.08    inference(forward_demodulation,[],[f5529,f5532])).
% 5.08/1.08  fof(f5532,plain,(
% 5.08/1.08    sK0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_521),
% 5.08/1.08    inference(avatar_component_clause,[],[f5531])).
% 5.08/1.08  fof(f5531,plain,(
% 5.08/1.08    spl3_521 <=> sK0 = k1_relat_1(k2_funct_1(sK2))),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_521])])).
% 5.08/1.08  fof(f5529,plain,(
% 5.08/1.08    k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | ~spl3_520),
% 5.08/1.08    inference(avatar_component_clause,[],[f5527])).
% 5.08/1.08  fof(f5527,plain,(
% 5.08/1.08    spl3_520 <=> k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_520])])).
% 5.08/1.08  fof(f5426,plain,(
% 5.08/1.08    k6_partfun1(sK0) != k2_funct_1(sK2) | spl3_504),
% 5.08/1.08    inference(avatar_component_clause,[],[f5424])).
% 5.08/1.08  fof(f5424,plain,(
% 5.08/1.08    spl3_504 <=> k6_partfun1(sK0) = k2_funct_1(sK2)),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_504])])).
% 5.08/1.08  fof(f5565,plain,(
% 5.08/1.08    ~spl3_1 | ~spl3_25 | ~spl3_12 | ~spl3_483 | spl3_521),
% 5.08/1.08    inference(avatar_split_clause,[],[f5564,f5531,f5264,f453,f545,f135])).
% 5.08/1.08  fof(f135,plain,(
% 5.08/1.08    spl3_1 <=> v1_relat_1(sK2)),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.08/1.08  fof(f545,plain,(
% 5.08/1.08    spl3_25 <=> v2_funct_1(sK2)),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 5.08/1.08  fof(f453,plain,(
% 5.08/1.08    spl3_12 <=> v1_funct_1(sK2)),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 5.08/1.08  fof(f5264,plain,(
% 5.08/1.08    spl3_483 <=> sK0 = k2_relat_1(sK2)),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_483])])).
% 5.08/1.08  fof(f5564,plain,(
% 5.08/1.08    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_483 | spl3_521)),
% 5.08/1.08    inference(trivial_inequality_removal,[],[f5563])).
% 5.08/1.08  fof(f5563,plain,(
% 5.08/1.08    sK0 != sK0 | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_483 | spl3_521)),
% 5.08/1.08    inference(forward_demodulation,[],[f5562,f5265])).
% 5.08/1.08  fof(f5265,plain,(
% 5.08/1.08    sK0 = k2_relat_1(sK2) | ~spl3_483),
% 5.08/1.08    inference(avatar_component_clause,[],[f5264])).
% 5.08/1.08  fof(f5562,plain,(
% 5.08/1.08    sK0 != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_521),
% 5.08/1.08    inference(superposition,[],[f5533,f87])).
% 5.08/1.08  fof(f87,plain,(
% 5.08/1.08    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.08/1.08    inference(cnf_transformation,[],[f40])).
% 5.08/1.08  fof(f40,plain,(
% 5.08/1.08    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.08/1.08    inference(flattening,[],[f39])).
% 5.08/1.08  fof(f39,plain,(
% 5.08/1.08    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.08/1.08    inference(ennf_transformation,[],[f15])).
% 5.08/1.08  fof(f15,axiom,(
% 5.08/1.08    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 5.08/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 5.08/1.08  fof(f5533,plain,(
% 5.08/1.08    sK0 != k1_relat_1(k2_funct_1(sK2)) | spl3_521),
% 5.08/1.08    inference(avatar_component_clause,[],[f5531])).
% 5.08/1.08  fof(f5544,plain,(
% 5.08/1.08    ~spl3_27 | ~spl3_26 | spl3_505 | ~spl3_519),
% 5.08/1.08    inference(avatar_split_clause,[],[f5539,f5493,f5428,f549,f553])).
% 5.08/1.08  fof(f553,plain,(
% 5.08/1.08    spl3_27 <=> v5_relat_1(k2_funct_1(sK2),sK0)),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 5.08/1.08  fof(f549,plain,(
% 5.08/1.08    spl3_26 <=> v1_relat_1(k2_funct_1(sK2))),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 5.08/1.08  fof(f5428,plain,(
% 5.08/1.08    spl3_505 <=> sK0 = k2_relat_1(k2_funct_1(sK2))),
% 5.08/1.08    introduced(avatar_definition,[new_symbols(naming,[spl3_505])])).
% 5.52/1.10  fof(f5493,plain,(
% 5.52/1.10    spl3_519 <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_519])])).
% 5.52/1.10  fof(f5539,plain,(
% 5.52/1.10    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v5_relat_1(k2_funct_1(sK2),sK0) | ~spl3_519),
% 5.52/1.10    inference(resolution,[],[f5495,f170])).
% 5.52/1.10  fof(f170,plain,(
% 5.52/1.10    ( ! [X2,X3] : (~r1_tarski(X2,k2_relat_1(X3)) | k2_relat_1(X3) = X2 | ~v1_relat_1(X3) | ~v5_relat_1(X3,X2)) )),
% 5.52/1.10    inference(resolution,[],[f104,f98])).
% 5.52/1.10  fof(f98,plain,(
% 5.52/1.10    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f50])).
% 5.52/1.10  fof(f50,plain,(
% 5.52/1.10    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 5.52/1.10    inference(ennf_transformation,[],[f4])).
% 5.52/1.10  fof(f4,axiom,(
% 5.52/1.10    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 5.52/1.10  fof(f104,plain,(
% 5.52/1.10    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 5.52/1.10    inference(cnf_transformation,[],[f1])).
% 5.52/1.10  fof(f1,axiom,(
% 5.52/1.10    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.52/1.10  fof(f5495,plain,(
% 5.52/1.10    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) | ~spl3_519),
% 5.52/1.10    inference(avatar_component_clause,[],[f5493])).
% 5.52/1.10  fof(f5534,plain,(
% 5.52/1.10    ~spl3_1 | ~spl3_34 | ~spl3_25 | ~spl3_15 | ~spl3_3 | ~spl3_12 | spl3_520 | ~spl3_35 | ~spl3_503 | ~spl3_26 | ~spl3_75 | ~spl3_521 | ~spl3_59 | ~spl3_71),
% 5.52/1.10    inference(avatar_split_clause,[],[f5525,f1339,f1147,f5531,f1397,f549,f5420,f603,f5527,f453,f144,f466,f545,f599,f135])).
% 5.52/1.10  fof(f599,plain,(
% 5.52/1.10    spl3_34 <=> v2_funct_1(sK1)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 5.52/1.10  fof(f466,plain,(
% 5.52/1.10    spl3_15 <=> v1_funct_1(sK1)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 5.52/1.10  fof(f144,plain,(
% 5.52/1.10    spl3_3 <=> v1_relat_1(sK1)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 5.52/1.10  fof(f603,plain,(
% 5.52/1.10    spl3_35 <=> v1_relat_1(k2_funct_1(sK1))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 5.52/1.10  fof(f5420,plain,(
% 5.52/1.10    spl3_503 <=> v1_funct_1(k2_funct_1(sK2))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_503])])).
% 5.52/1.10  fof(f1397,plain,(
% 5.52/1.10    spl3_75 <=> v1_funct_1(k2_funct_1(sK1))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 5.52/1.10  fof(f1147,plain,(
% 5.52/1.10    spl3_59 <=> sK1 = k5_relat_1(sK2,sK1)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 5.52/1.10  fof(f1339,plain,(
% 5.52/1.10    spl3_71 <=> sK0 = k2_relat_1(k2_funct_1(sK1))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 5.52/1.10  fof(f5525,plain,(
% 5.52/1.10    sK0 != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | ~v2_funct_1(sK1) | ~v1_relat_1(sK2) | (~spl3_59 | ~spl3_71)),
% 5.52/1.10    inference(forward_demodulation,[],[f5522,f1341])).
% 5.52/1.10  fof(f1341,plain,(
% 5.52/1.10    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~spl3_71),
% 5.52/1.10    inference(avatar_component_clause,[],[f1339])).
% 5.52/1.10  fof(f5522,plain,(
% 5.52/1.10    ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | ~v2_funct_1(sK1) | ~v1_relat_1(sK2) | ~spl3_59),
% 5.52/1.10    inference(trivial_inequality_removal,[],[f5517])).
% 5.52/1.10  fof(f5517,plain,(
% 5.52/1.10    k2_funct_1(sK1) != k2_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | k2_funct_1(sK2) = k6_partfun1(k1_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | ~v2_funct_1(sK1) | ~v1_relat_1(sK2) | ~spl3_59),
% 5.52/1.10    inference(superposition,[],[f854,f1149])).
% 5.52/1.10  fof(f1149,plain,(
% 5.52/1.10    sK1 = k5_relat_1(sK2,sK1) | ~spl3_59),
% 5.52/1.10    inference(avatar_component_clause,[],[f1147])).
% 5.52/1.10  fof(f854,plain,(
% 5.52/1.10    ( ! [X2,X1] : (k2_funct_1(X1) != k2_funct_1(k5_relat_1(X2,X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X2)) | ~v1_funct_1(k2_funct_1(X2)) | k2_relat_1(k2_funct_1(X1)) != k1_relat_1(k2_funct_1(X2)) | ~v1_relat_1(k2_funct_1(X1)) | k2_funct_1(X2) = k6_partfun1(k1_relat_1(k2_funct_1(X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X2) | ~v2_funct_1(X1) | ~v1_relat_1(X2)) )),
% 5.52/1.10    inference(superposition,[],[f123,f91])).
% 5.52/1.10  fof(f91,plain,(
% 5.52/1.10    ( ! [X0,X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f44])).
% 5.52/1.10  fof(f44,plain,(
% 5.52/1.10    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.52/1.10    inference(flattening,[],[f43])).
% 5.52/1.10  fof(f43,plain,(
% 5.52/1.10    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.52/1.10    inference(ennf_transformation,[],[f17])).
% 5.52/1.10  fof(f17,axiom,(
% 5.52/1.10    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).
% 5.52/1.10  fof(f123,plain,(
% 5.52/1.10    ( ! [X0,X1] : (k5_relat_1(X0,X1) != X0 | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 5.52/1.10    inference(definition_unfolding,[],[f94,f77])).
% 5.52/1.10  fof(f77,plain,(
% 5.52/1.10    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f24])).
% 5.52/1.10  fof(f24,axiom,(
% 5.52/1.10    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 5.52/1.10  fof(f94,plain,(
% 5.52/1.10    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != X0 | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 5.52/1.10    inference(cnf_transformation,[],[f48])).
% 5.52/1.10  fof(f48,plain,(
% 5.52/1.10    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.52/1.10    inference(flattening,[],[f47])).
% 5.52/1.10  fof(f47,plain,(
% 5.52/1.10    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.52/1.10    inference(ennf_transformation,[],[f13])).
% 5.52/1.10  fof(f13,axiom,(
% 5.52/1.10    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 5.52/1.10  fof(f5513,plain,(
% 5.52/1.10    ~spl3_1 | spl3_503),
% 5.52/1.10    inference(avatar_contradiction_clause,[],[f5510])).
% 5.52/1.10  fof(f5510,plain,(
% 5.52/1.10    $false | (~spl3_1 | spl3_503)),
% 5.52/1.10    inference(unit_resulting_resolution,[],[f137,f68,f5422,f86])).
% 5.52/1.10  fof(f86,plain,(
% 5.52/1.10    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f38])).
% 5.52/1.10  fof(f38,plain,(
% 5.52/1.10    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.52/1.10    inference(flattening,[],[f37])).
% 5.52/1.10  fof(f37,plain,(
% 5.52/1.10    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.52/1.10    inference(ennf_transformation,[],[f11])).
% 5.52/1.10  fof(f11,axiom,(
% 5.52/1.10    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 5.52/1.10  fof(f5422,plain,(
% 5.52/1.10    ~v1_funct_1(k2_funct_1(sK2)) | spl3_503),
% 5.52/1.10    inference(avatar_component_clause,[],[f5420])).
% 5.52/1.10  fof(f68,plain,(
% 5.52/1.10    v1_funct_1(sK2)),
% 5.52/1.10    inference(cnf_transformation,[],[f31])).
% 5.52/1.10  fof(f137,plain,(
% 5.52/1.10    v1_relat_1(sK2) | ~spl3_1),
% 5.52/1.10    inference(avatar_component_clause,[],[f135])).
% 5.52/1.10  fof(f5496,plain,(
% 5.52/1.10    ~spl3_1 | ~spl3_25 | ~spl3_12 | ~spl3_26 | spl3_519 | ~spl3_18),
% 5.52/1.10    inference(avatar_split_clause,[],[f1312,f489,f5493,f549,f453,f545,f135])).
% 5.52/1.10  fof(f489,plain,(
% 5.52/1.10    spl3_18 <=> sK0 = k1_relat_1(sK2)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 5.52/1.10  fof(f1312,plain,(
% 5.52/1.10    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_18),
% 5.52/1.10    inference(superposition,[],[f1240,f491])).
% 5.52/1.10  fof(f491,plain,(
% 5.52/1.10    sK0 = k1_relat_1(sK2) | ~spl3_18),
% 5.52/1.10    inference(avatar_component_clause,[],[f489])).
% 5.52/1.10  fof(f1240,plain,(
% 5.52/1.10    ( ! [X1] : (r1_tarski(k1_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.52/1.10    inference(duplicate_literal_removal,[],[f1231])).
% 5.52/1.10  fof(f1231,plain,(
% 5.52/1.10    ( ! [X1] : (~v1_relat_1(k2_funct_1(X1)) | r1_tarski(k1_relat_1(X1),k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X1))) )),
% 5.52/1.10    inference(resolution,[],[f302,f160])).
% 5.52/1.10  fof(f160,plain,(
% 5.52/1.10    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.52/1.10    inference(resolution,[],[f97,f124])).
% 5.52/1.10  fof(f124,plain,(
% 5.52/1.10    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.52/1.10    inference(equality_resolution,[],[f103])).
% 5.52/1.10  fof(f103,plain,(
% 5.52/1.10    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.52/1.10    inference(cnf_transformation,[],[f1])).
% 5.52/1.10  fof(f97,plain,(
% 5.52/1.10    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | v5_relat_1(X1,X0)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f50])).
% 5.52/1.10  fof(f302,plain,(
% 5.52/1.10    ( ! [X6,X5] : (~v5_relat_1(k2_funct_1(X5),X6) | ~v1_relat_1(k2_funct_1(X5)) | r1_tarski(k1_relat_1(X5),X6) | ~v1_funct_1(X5) | ~v2_funct_1(X5) | ~v1_relat_1(X5)) )),
% 5.52/1.10    inference(superposition,[],[f98,f88])).
% 5.52/1.10  fof(f88,plain,(
% 5.52/1.10    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f40])).
% 5.52/1.10  fof(f5431,plain,(
% 5.52/1.10    ~spl3_25 | ~spl3_26 | ~spl3_12 | ~spl3_1 | ~spl3_503 | ~spl3_504 | ~spl3_505 | spl3_51 | ~spl3_18 | ~spl3_483),
% 5.52/1.10    inference(avatar_split_clause,[],[f5418,f5264,f489,f737,f5428,f5424,f5420,f135,f453,f549,f545])).
% 5.52/1.10  fof(f5418,plain,(
% 5.52/1.10    sK2 = k6_partfun1(sK0) | sK0 != k2_relat_1(k2_funct_1(sK2)) | k6_partfun1(sK0) != k2_funct_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_18 | ~spl3_483)),
% 5.52/1.10    inference(forward_demodulation,[],[f5417,f491])).
% 5.52/1.10  fof(f5417,plain,(
% 5.52/1.10    sK0 != k2_relat_1(k2_funct_1(sK2)) | k6_partfun1(sK0) != k2_funct_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | sK2 = k6_partfun1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_18 | ~spl3_483)),
% 5.52/1.10    inference(forward_demodulation,[],[f5325,f491])).
% 5.52/1.10  fof(f5325,plain,(
% 5.52/1.10    k6_partfun1(sK0) != k2_funct_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | sK2 = k6_partfun1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~spl3_483),
% 5.52/1.10    inference(superposition,[],[f857,f5265])).
% 5.52/1.10  fof(f857,plain,(
% 5.52/1.10    ( ! [X0] : (k2_funct_1(X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | k6_partfun1(k1_relat_1(X0)) = X0 | ~v2_funct_1(X0)) )),
% 5.52/1.10    inference(duplicate_literal_removal,[],[f853])).
% 5.52/1.10  fof(f853,plain,(
% 5.52/1.10    ( ! [X0] : (k2_funct_1(X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | k6_partfun1(k1_relat_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.52/1.10    inference(superposition,[],[f123,f121])).
% 5.52/1.10  fof(f121,plain,(
% 5.52/1.10    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.52/1.10    inference(definition_unfolding,[],[f90,f77])).
% 5.52/1.10  fof(f90,plain,(
% 5.52/1.10    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 5.52/1.10    inference(cnf_transformation,[],[f42])).
% 5.52/1.10  fof(f42,plain,(
% 5.52/1.10    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.52/1.10    inference(flattening,[],[f41])).
% 5.52/1.10  fof(f41,plain,(
% 5.52/1.10    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.52/1.10    inference(ennf_transformation,[],[f16])).
% 5.52/1.10  fof(f16,axiom,(
% 5.52/1.10    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 5.52/1.10  fof(f5376,plain,(
% 5.52/1.10    ~spl3_1 | ~spl3_12 | spl3_25 | ~spl3_34 | ~spl3_39 | ~spl3_59 | ~spl3_483),
% 5.52/1.10    inference(avatar_split_clause,[],[f5375,f5264,f1147,f641,f599,f545,f453,f135])).
% 5.52/1.10  fof(f641,plain,(
% 5.52/1.10    spl3_39 <=> ! [X4] : (sK0 != k2_relat_1(X4) | v2_funct_1(X4) | ~v2_funct_1(k5_relat_1(X4,sK1)) | ~v1_funct_1(X4) | ~v1_relat_1(X4))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 5.52/1.10  fof(f5375,plain,(
% 5.52/1.10    ~v2_funct_1(sK1) | v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_39 | ~spl3_59 | ~spl3_483)),
% 5.52/1.10    inference(forward_demodulation,[],[f5337,f1149])).
% 5.52/1.10  fof(f5337,plain,(
% 5.52/1.10    v2_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_39 | ~spl3_483)),
% 5.52/1.10    inference(trivial_inequality_removal,[],[f5317])).
% 5.52/1.10  fof(f5317,plain,(
% 5.52/1.10    sK0 != sK0 | v2_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_39 | ~spl3_483)),
% 5.52/1.10    inference(superposition,[],[f642,f5265])).
% 5.52/1.10  fof(f642,plain,(
% 5.52/1.10    ( ! [X4] : (sK0 != k2_relat_1(X4) | v2_funct_1(X4) | ~v2_funct_1(k5_relat_1(X4,sK1)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) ) | ~spl3_39),
% 5.52/1.10    inference(avatar_component_clause,[],[f641])).
% 5.52/1.10  fof(f5286,plain,(
% 5.52/1.10    ~spl3_1 | spl3_484),
% 5.52/1.10    inference(avatar_contradiction_clause,[],[f5284])).
% 5.52/1.10  fof(f5284,plain,(
% 5.52/1.10    $false | (~spl3_1 | spl3_484)),
% 5.52/1.10    inference(unit_resulting_resolution,[],[f137,f194,f5273,f98])).
% 5.52/1.10  fof(f5273,plain,(
% 5.52/1.10    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_484),
% 5.52/1.10    inference(avatar_component_clause,[],[f5271])).
% 5.52/1.10  fof(f5271,plain,(
% 5.52/1.10    spl3_484 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_484])])).
% 5.52/1.10  fof(f194,plain,(
% 5.52/1.10    v5_relat_1(sK2,sK0)),
% 5.52/1.10    inference(resolution,[],[f110,f70])).
% 5.52/1.10  fof(f110,plain,(
% 5.52/1.10    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f59])).
% 5.52/1.10  fof(f59,plain,(
% 5.52/1.10    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.52/1.10    inference(ennf_transformation,[],[f18])).
% 5.52/1.10  fof(f18,axiom,(
% 5.52/1.10    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 5.52/1.10  fof(f5274,plain,(
% 5.52/1.10    ~spl3_1 | ~spl3_3 | ~spl3_34 | ~spl3_15 | spl3_483 | ~spl3_484 | ~spl3_20 | ~spl3_59 | ~spl3_130),
% 5.52/1.10    inference(avatar_split_clause,[],[f5269,f2092,f1147,f501,f5271,f5264,f466,f599,f144,f135])).
% 5.52/1.10  fof(f501,plain,(
% 5.52/1.10    spl3_20 <=> sK0 = k1_relat_1(sK1)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 5.52/1.10  fof(f2092,plain,(
% 5.52/1.10    spl3_130 <=> sK0 = k10_relat_1(sK1,k2_relat_1(sK1))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_130])])).
% 5.52/1.10  fof(f5269,plain,(
% 5.52/1.10    ~r1_tarski(k2_relat_1(sK2),sK0) | sK0 = k2_relat_1(sK2) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | (~spl3_20 | ~spl3_59 | ~spl3_130)),
% 5.52/1.10    inference(forward_demodulation,[],[f5268,f503])).
% 5.52/1.10  fof(f503,plain,(
% 5.52/1.10    sK0 = k1_relat_1(sK1) | ~spl3_20),
% 5.52/1.10    inference(avatar_component_clause,[],[f501])).
% 5.52/1.10  fof(f5268,plain,(
% 5.52/1.10    sK0 = k2_relat_1(sK2) | ~v1_funct_1(sK1) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | (~spl3_59 | ~spl3_130)),
% 5.52/1.10    inference(forward_demodulation,[],[f5257,f2094])).
% 5.52/1.10  fof(f2094,plain,(
% 5.52/1.10    sK0 = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl3_130),
% 5.52/1.10    inference(avatar_component_clause,[],[f2092])).
% 5.52/1.10  fof(f5257,plain,(
% 5.52/1.10    k2_relat_1(sK2) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~r1_tarski(k2_relat_1(sK2),k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~spl3_59),
% 5.52/1.10    inference(superposition,[],[f413,f1149])).
% 5.52/1.10  fof(f413,plain,(
% 5.52/1.10    ( ! [X2,X3] : (k2_relat_1(X3) = k10_relat_1(X2,k2_relat_1(k5_relat_1(X3,X2))) | ~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X2)) | ~v2_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X3)) )),
% 5.52/1.10    inference(duplicate_literal_removal,[],[f412])).
% 5.52/1.10  fof(f412,plain,(
% 5.52/1.10    ( ! [X2,X3] : (k2_relat_1(X3) = k10_relat_1(X2,k2_relat_1(k5_relat_1(X3,X2))) | ~v1_funct_1(X2) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X2)) | ~v2_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X3)) )),
% 5.52/1.10    inference(superposition,[],[f99,f81])).
% 5.52/1.10  fof(f81,plain,(
% 5.52/1.10    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f33])).
% 5.52/1.10  fof(f33,plain,(
% 5.52/1.10    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 5.52/1.10    inference(ennf_transformation,[],[f7])).
% 5.52/1.10  fof(f7,axiom,(
% 5.52/1.10    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 5.52/1.10  fof(f99,plain,(
% 5.52/1.10    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f52])).
% 5.52/1.10  fof(f52,plain,(
% 5.52/1.10    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.52/1.10    inference(flattening,[],[f51])).
% 5.52/1.10  fof(f51,plain,(
% 5.52/1.10    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 5.52/1.10    inference(ennf_transformation,[],[f12])).
% 5.52/1.10  fof(f12,axiom,(
% 5.52/1.10    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 5.52/1.10  fof(f5249,plain,(
% 5.52/1.10    ~spl3_12 | ~spl3_19 | ~spl3_15 | ~spl3_17 | spl3_59 | ~spl3_56),
% 5.52/1.10    inference(avatar_split_clause,[],[f5240,f775,f1147,f485,f466,f497,f453])).
% 5.52/1.10  fof(f497,plain,(
% 5.52/1.10    spl3_19 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 5.52/1.10  fof(f485,plain,(
% 5.52/1.10    spl3_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 5.52/1.10  fof(f775,plain,(
% 5.52/1.10    spl3_56 <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 5.52/1.10    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 5.52/1.10  fof(f5240,plain,(
% 5.52/1.10    sK1 = k5_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~spl3_56),
% 5.52/1.10    inference(superposition,[],[f116,f777])).
% 5.52/1.10  fof(f777,plain,(
% 5.52/1.10    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~spl3_56),
% 5.52/1.10    inference(avatar_component_clause,[],[f775])).
% 5.52/1.10  fof(f116,plain,(
% 5.52/1.10    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f65])).
% 5.52/1.10  fof(f65,plain,(
% 5.52/1.10    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 5.52/1.10    inference(flattening,[],[f64])).
% 5.52/1.10  fof(f64,plain,(
% 5.52/1.10    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 5.52/1.10    inference(ennf_transformation,[],[f23])).
% 5.52/1.10  fof(f23,axiom,(
% 5.52/1.10    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 5.52/1.10  fof(f4140,plain,(
% 5.52/1.10    spl3_55),
% 5.52/1.10    inference(avatar_contradiction_clause,[],[f4128])).
% 5.52/1.10  fof(f4128,plain,(
% 5.52/1.10    $false | spl3_55),
% 5.52/1.10    inference(unit_resulting_resolution,[],[f74,f68,f70,f76,f773,f1196])).
% 5.52/1.10  fof(f1196,plain,(
% 5.52/1.10    ( ! [X57,X54,X52,X56,X55,X53] : (r1_tarski(k1_partfun1(X53,X54,X56,X57,X52,X55),k2_zfmisc_1(X53,X57)) | ~v1_funct_1(X55) | ~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) | ~v1_funct_1(X52) | ~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))) )),
% 5.52/1.10    inference(resolution,[],[f118,f106])).
% 5.52/1.10  fof(f106,plain,(
% 5.52/1.10    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f2])).
% 5.52/1.10  fof(f2,axiom,(
% 5.52/1.10    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.52/1.10    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 5.52/1.10  fof(f118,plain,(
% 5.52/1.10    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 5.52/1.10    inference(cnf_transformation,[],[f67])).
% 5.52/1.10  fof(f67,plain,(
% 5.52/1.10    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 5.52/1.10    inference(flattening,[],[f66])).
% 5.52/1.11  fof(f66,plain,(
% 5.52/1.11    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 5.52/1.11    inference(ennf_transformation,[],[f22])).
% 5.52/1.12  fof(f22,axiom,(
% 5.52/1.12    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 5.52/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 5.52/1.12  fof(f773,plain,(
% 5.52/1.12    ~r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k2_zfmisc_1(sK0,sK0)) | spl3_55),
% 5.52/1.12    inference(avatar_component_clause,[],[f771])).
% 5.52/1.12  fof(f771,plain,(
% 5.52/1.12    spl3_55 <=> r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k2_zfmisc_1(sK0,sK0))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 5.52/1.12  fof(f76,plain,(
% 5.52/1.12    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 5.52/1.12    inference(cnf_transformation,[],[f31])).
% 5.52/1.12  fof(f74,plain,(
% 5.52/1.12    v1_funct_1(sK1)),
% 5.52/1.12    inference(cnf_transformation,[],[f31])).
% 5.52/1.12  fof(f2136,plain,(
% 5.52/1.12    spl3_131),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f2132])).
% 5.52/1.12  fof(f2132,plain,(
% 5.52/1.12    $false | spl3_131),
% 5.52/1.12    inference(unit_resulting_resolution,[],[f124,f2098])).
% 5.52/1.12  fof(f2098,plain,(
% 5.52/1.12    ~r1_tarski(sK0,sK0) | spl3_131),
% 5.52/1.12    inference(avatar_component_clause,[],[f2096])).
% 5.52/1.12  fof(f2096,plain,(
% 5.52/1.12    spl3_131 <=> r1_tarski(sK0,sK0)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_131])])).
% 5.52/1.12  fof(f2099,plain,(
% 5.52/1.12    ~spl3_3 | ~spl3_34 | ~spl3_15 | spl3_130 | ~spl3_131 | ~spl3_20 | ~spl3_128),
% 5.52/1.12    inference(avatar_split_clause,[],[f2090,f2061,f501,f2096,f2092,f466,f599,f144])).
% 5.52/1.12  fof(f2061,plain,(
% 5.52/1.12    spl3_128 <=> k2_relat_1(sK1) = k9_relat_1(sK1,sK0)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_128])])).
% 5.52/1.12  fof(f2090,plain,(
% 5.52/1.12    ~r1_tarski(sK0,sK0) | sK0 = k10_relat_1(sK1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_20 | ~spl3_128)),
% 5.52/1.12    inference(forward_demodulation,[],[f2075,f503])).
% 5.52/1.12  fof(f2075,plain,(
% 5.52/1.12    sK0 = k10_relat_1(sK1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~r1_tarski(sK0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_128),
% 5.52/1.12    inference(superposition,[],[f99,f2063])).
% 5.52/1.12  fof(f2063,plain,(
% 5.52/1.12    k2_relat_1(sK1) = k9_relat_1(sK1,sK0) | ~spl3_128),
% 5.52/1.12    inference(avatar_component_clause,[],[f2061])).
% 5.52/1.12  fof(f2064,plain,(
% 5.52/1.12    ~spl3_34 | ~spl3_15 | ~spl3_3 | spl3_128 | ~spl3_74),
% 5.52/1.12    inference(avatar_split_clause,[],[f2059,f1393,f2061,f144,f466,f599])).
% 5.52/1.12  fof(f1393,plain,(
% 5.52/1.12    spl3_74 <=> ! [X0] : (k2_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(X0,sK0) | ~v1_relat_1(X0))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 5.52/1.12  fof(f2059,plain,(
% 5.52/1.12    k2_relat_1(sK1) = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~spl3_74),
% 5.52/1.12    inference(forward_demodulation,[],[f2058,f119])).
% 5.52/1.12  fof(f119,plain,(
% 5.52/1.12    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 5.52/1.12    inference(definition_unfolding,[],[f79,f77])).
% 5.52/1.12  fof(f79,plain,(
% 5.52/1.12    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 5.52/1.12    inference(cnf_transformation,[],[f10])).
% 5.52/1.12  fof(f10,axiom,(
% 5.52/1.12    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 5.52/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 5.52/1.12  fof(f2058,plain,(
% 5.52/1.12    k2_relat_1(k6_partfun1(k2_relat_1(sK1))) = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~spl3_74),
% 5.52/1.12    inference(duplicate_literal_removal,[],[f2010])).
% 5.52/1.12  fof(f2010,plain,(
% 5.52/1.12    k2_relat_1(k6_partfun1(k2_relat_1(sK1))) = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_74),
% 5.52/1.12    inference(superposition,[],[f1394,f121])).
% 5.52/1.12  fof(f1394,plain,(
% 5.52/1.12    ( ! [X0] : (k2_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(X0,sK0) | ~v1_relat_1(X0)) ) | ~spl3_74),
% 5.52/1.12    inference(avatar_component_clause,[],[f1393])).
% 5.52/1.12  fof(f1503,plain,(
% 5.52/1.12    ~spl3_3 | spl3_75),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f1501])).
% 5.52/1.12  fof(f1501,plain,(
% 5.52/1.12    $false | (~spl3_3 | spl3_75)),
% 5.52/1.12    inference(unit_resulting_resolution,[],[f146,f74,f1399,f86])).
% 5.52/1.12  fof(f1399,plain,(
% 5.52/1.12    ~v1_funct_1(k2_funct_1(sK1)) | spl3_75),
% 5.52/1.12    inference(avatar_component_clause,[],[f1397])).
% 5.52/1.12  fof(f146,plain,(
% 5.52/1.12    v1_relat_1(sK1) | ~spl3_3),
% 5.52/1.12    inference(avatar_component_clause,[],[f144])).
% 5.52/1.12  fof(f1395,plain,(
% 5.52/1.12    ~spl3_35 | spl3_74 | ~spl3_71),
% 5.52/1.12    inference(avatar_split_clause,[],[f1356,f1339,f1393,f603])).
% 5.52/1.12  fof(f1356,plain,(
% 5.52/1.12    ( ! [X0] : (k2_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k9_relat_1(X0,sK0) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK1))) ) | ~spl3_71),
% 5.52/1.12    inference(superposition,[],[f81,f1341])).
% 5.52/1.12  fof(f1342,plain,(
% 5.52/1.12    ~spl3_36 | ~spl3_35 | spl3_71 | ~spl3_70),
% 5.52/1.12    inference(avatar_split_clause,[],[f1333,f1318,f1339,f603,f607])).
% 5.52/1.12  fof(f607,plain,(
% 5.52/1.12    spl3_36 <=> v5_relat_1(k2_funct_1(sK1),sK0)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 5.52/1.12  fof(f1318,plain,(
% 5.52/1.12    spl3_70 <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1)))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 5.52/1.12  fof(f1333,plain,(
% 5.52/1.12    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v5_relat_1(k2_funct_1(sK1),sK0) | ~spl3_70),
% 5.52/1.12    inference(resolution,[],[f1320,f170])).
% 5.52/1.12  fof(f1320,plain,(
% 5.52/1.12    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) | ~spl3_70),
% 5.52/1.12    inference(avatar_component_clause,[],[f1318])).
% 5.52/1.12  fof(f1321,plain,(
% 5.52/1.12    ~spl3_3 | ~spl3_34 | ~spl3_15 | ~spl3_35 | spl3_70 | ~spl3_20),
% 5.52/1.12    inference(avatar_split_clause,[],[f1311,f501,f1318,f603,f466,f599,f144])).
% 5.52/1.12  fof(f1311,plain,(
% 5.52/1.12    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_20),
% 5.52/1.12    inference(superposition,[],[f1240,f503])).
% 5.52/1.12  fof(f778,plain,(
% 5.52/1.12    ~spl3_55 | spl3_56),
% 5.52/1.12    inference(avatar_split_clause,[],[f768,f775,f771])).
% 5.52/1.12  fof(f768,plain,(
% 5.52/1.12    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k2_zfmisc_1(sK0,sK0))),
% 5.52/1.12    inference(resolution,[],[f753,f71])).
% 5.52/1.12  fof(f71,plain,(
% 5.52/1.12    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 5.52/1.12    inference(cnf_transformation,[],[f31])).
% 5.52/1.12  fof(f753,plain,(
% 5.52/1.12    ( ! [X0] : (~r2_relset_1(sK0,sK0,X0,sK1) | sK1 = X0 | ~r1_tarski(X0,k2_zfmisc_1(sK0,sK0))) )),
% 5.52/1.12    inference(resolution,[],[f695,f105])).
% 5.52/1.12  fof(f105,plain,(
% 5.52/1.12    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f2])).
% 5.52/1.12  fof(f695,plain,(
% 5.52/1.12    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X1 | ~r2_relset_1(sK0,sK0,X1,sK1)) )),
% 5.52/1.12    inference(resolution,[],[f115,f76])).
% 5.52/1.12  fof(f115,plain,(
% 5.52/1.12    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f63])).
% 5.52/1.12  fof(f692,plain,(
% 5.52/1.12    ~spl3_1 | spl3_26),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f690])).
% 5.52/1.12  fof(f690,plain,(
% 5.52/1.12    $false | (~spl3_1 | spl3_26)),
% 5.52/1.12    inference(unit_resulting_resolution,[],[f137,f68,f551,f85])).
% 5.52/1.12  fof(f85,plain,(
% 5.52/1.12    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f38])).
% 5.52/1.12  fof(f551,plain,(
% 5.52/1.12    ~v1_relat_1(k2_funct_1(sK2)) | spl3_26),
% 5.52/1.12    inference(avatar_component_clause,[],[f549])).
% 5.52/1.12  fof(f643,plain,(
% 5.52/1.12    ~spl3_3 | ~spl3_15 | spl3_39 | ~spl3_20),
% 5.52/1.12    inference(avatar_split_clause,[],[f638,f501,f641,f466,f144])).
% 5.52/1.12  fof(f638,plain,(
% 5.52/1.12    ( ! [X4] : (sK0 != k2_relat_1(X4) | ~v1_funct_1(sK1) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~v2_funct_1(k5_relat_1(X4,sK1)) | ~v1_relat_1(sK1) | v2_funct_1(X4)) ) | ~spl3_20),
% 5.52/1.12    inference(superposition,[],[f92,f503])).
% 5.52/1.12  fof(f92,plain,(
% 5.52/1.12    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f46])).
% 5.52/1.12  fof(f46,plain,(
% 5.52/1.12    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 5.52/1.12    inference(flattening,[],[f45])).
% 5.52/1.12  fof(f45,plain,(
% 5.52/1.12    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 5.52/1.12    inference(ennf_transformation,[],[f14])).
% 5.52/1.12  fof(f14,axiom,(
% 5.52/1.12    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 5.52/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 5.52/1.12  fof(f630,plain,(
% 5.52/1.12    ~spl3_3 | spl3_35),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f628])).
% 5.52/1.12  fof(f628,plain,(
% 5.52/1.12    $false | (~spl3_3 | spl3_35)),
% 5.52/1.12    inference(unit_resulting_resolution,[],[f146,f74,f605,f85])).
% 5.52/1.12  fof(f605,plain,(
% 5.52/1.12    ~v1_relat_1(k2_funct_1(sK1)) | spl3_35),
% 5.52/1.12    inference(avatar_component_clause,[],[f603])).
% 5.52/1.12  fof(f627,plain,(
% 5.52/1.12    spl3_34),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f626])).
% 5.52/1.12  fof(f626,plain,(
% 5.52/1.12    $false | spl3_34),
% 5.52/1.12    inference(subsumption_resolution,[],[f72,f601])).
% 5.52/1.12  fof(f601,plain,(
% 5.52/1.12    ~v2_funct_1(sK1) | spl3_34),
% 5.52/1.12    inference(avatar_component_clause,[],[f599])).
% 5.52/1.12  fof(f72,plain,(
% 5.52/1.12    v2_funct_1(sK1)),
% 5.52/1.12    inference(cnf_transformation,[],[f31])).
% 5.52/1.12  fof(f610,plain,(
% 5.52/1.12    ~spl3_3 | ~spl3_34 | ~spl3_15 | ~spl3_35 | spl3_36 | ~spl3_20),
% 5.52/1.12    inference(avatar_split_clause,[],[f576,f501,f607,f603,f466,f599,f144])).
% 5.52/1.12  fof(f576,plain,(
% 5.52/1.12    v5_relat_1(k2_funct_1(sK1),sK0) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_20),
% 5.52/1.12    inference(superposition,[],[f303,f503])).
% 5.52/1.12  fof(f303,plain,(
% 5.52/1.12    ( ! [X7] : (v5_relat_1(k2_funct_1(X7),k1_relat_1(X7)) | ~v1_relat_1(k2_funct_1(X7)) | ~v1_funct_1(X7) | ~v2_funct_1(X7) | ~v1_relat_1(X7)) )),
% 5.52/1.12    inference(superposition,[],[f160,f88])).
% 5.52/1.12  fof(f570,plain,(
% 5.52/1.12    spl3_19),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f566])).
% 5.52/1.12  fof(f566,plain,(
% 5.52/1.12    $false | spl3_19),
% 5.52/1.12    inference(subsumption_resolution,[],[f76,f499])).
% 5.52/1.12  fof(f499,plain,(
% 5.52/1.12    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_19),
% 5.52/1.12    inference(avatar_component_clause,[],[f497])).
% 5.52/1.12  fof(f556,plain,(
% 5.52/1.12    ~spl3_1 | ~spl3_25 | ~spl3_12 | ~spl3_26 | spl3_27 | ~spl3_18),
% 5.52/1.12    inference(avatar_split_clause,[],[f522,f489,f553,f549,f453,f545,f135])).
% 5.52/1.12  fof(f522,plain,(
% 5.52/1.12    v5_relat_1(k2_funct_1(sK2),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_18),
% 5.52/1.12    inference(superposition,[],[f303,f491])).
% 5.52/1.12  fof(f510,plain,(
% 5.52/1.12    spl3_17),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f506])).
% 5.52/1.12  fof(f506,plain,(
% 5.52/1.12    $false | spl3_17),
% 5.52/1.12    inference(subsumption_resolution,[],[f70,f487])).
% 5.52/1.12  fof(f487,plain,(
% 5.52/1.12    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_17),
% 5.52/1.12    inference(avatar_component_clause,[],[f485])).
% 5.52/1.12  fof(f505,plain,(
% 5.52/1.12    ~spl3_19 | spl3_20 | ~spl3_14),
% 5.52/1.12    inference(avatar_split_clause,[],[f495,f462,f501,f497])).
% 5.52/1.12  fof(f462,plain,(
% 5.52/1.12    spl3_14 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 5.52/1.12  fof(f495,plain,(
% 5.52/1.12    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_14),
% 5.52/1.12    inference(superposition,[],[f107,f464])).
% 5.52/1.12  fof(f464,plain,(
% 5.52/1.12    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_14),
% 5.52/1.12    inference(avatar_component_clause,[],[f462])).
% 5.52/1.12  fof(f107,plain,(
% 5.52/1.12    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.52/1.12    inference(cnf_transformation,[],[f57])).
% 5.52/1.12  fof(f57,plain,(
% 5.52/1.12    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.52/1.12    inference(ennf_transformation,[],[f19])).
% 5.52/1.12  fof(f19,axiom,(
% 5.52/1.12    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 5.52/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 5.52/1.12  fof(f493,plain,(
% 5.52/1.12    ~spl3_17 | spl3_18 | ~spl3_11),
% 5.52/1.12    inference(avatar_split_clause,[],[f483,f449,f489,f485])).
% 5.52/1.12  fof(f449,plain,(
% 5.52/1.12    spl3_11 <=> sK0 = k1_relset_1(sK0,sK0,sK2)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 5.52/1.12  fof(f483,plain,(
% 5.52/1.12    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_11),
% 5.52/1.12    inference(superposition,[],[f107,f451])).
% 5.52/1.12  fof(f451,plain,(
% 5.52/1.12    sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_11),
% 5.52/1.12    inference(avatar_component_clause,[],[f449])).
% 5.52/1.12  fof(f481,plain,(
% 5.52/1.12    spl3_15),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f480])).
% 5.52/1.12  fof(f480,plain,(
% 5.52/1.12    $false | spl3_15),
% 5.52/1.12    inference(subsumption_resolution,[],[f74,f468])).
% 5.52/1.12  fof(f468,plain,(
% 5.52/1.12    ~v1_funct_1(sK1) | spl3_15),
% 5.52/1.12    inference(avatar_component_clause,[],[f466])).
% 5.52/1.12  fof(f479,plain,(
% 5.52/1.12    spl3_16),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f478])).
% 5.52/1.12  fof(f478,plain,(
% 5.52/1.12    $false | spl3_16),
% 5.52/1.12    inference(subsumption_resolution,[],[f75,f472])).
% 5.52/1.12  fof(f472,plain,(
% 5.52/1.12    ~v1_funct_2(sK1,sK0,sK0) | spl3_16),
% 5.52/1.12    inference(avatar_component_clause,[],[f470])).
% 5.52/1.12  fof(f470,plain,(
% 5.52/1.12    spl3_16 <=> v1_funct_2(sK1,sK0,sK0)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 5.52/1.12  fof(f75,plain,(
% 5.52/1.12    v1_funct_2(sK1,sK0,sK0)),
% 5.52/1.12    inference(cnf_transformation,[],[f31])).
% 5.52/1.12  fof(f477,plain,(
% 5.52/1.12    spl3_13),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f476])).
% 5.52/1.12  fof(f476,plain,(
% 5.52/1.12    $false | spl3_13),
% 5.52/1.12    inference(subsumption_resolution,[],[f69,f459])).
% 5.52/1.12  fof(f459,plain,(
% 5.52/1.12    ~v1_funct_2(sK2,sK0,sK0) | spl3_13),
% 5.52/1.12    inference(avatar_component_clause,[],[f457])).
% 5.52/1.12  fof(f457,plain,(
% 5.52/1.12    spl3_13 <=> v1_funct_2(sK2,sK0,sK0)),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 5.52/1.12  fof(f69,plain,(
% 5.52/1.12    v1_funct_2(sK2,sK0,sK0)),
% 5.52/1.12    inference(cnf_transformation,[],[f31])).
% 5.52/1.12  fof(f475,plain,(
% 5.52/1.12    spl3_12),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f474])).
% 5.52/1.12  fof(f474,plain,(
% 5.52/1.12    $false | spl3_12),
% 5.52/1.12    inference(subsumption_resolution,[],[f68,f455])).
% 5.52/1.12  fof(f455,plain,(
% 5.52/1.12    ~v1_funct_1(sK2) | spl3_12),
% 5.52/1.12    inference(avatar_component_clause,[],[f453])).
% 5.52/1.12  fof(f473,plain,(
% 5.52/1.12    spl3_14 | ~spl3_15 | ~spl3_16),
% 5.52/1.12    inference(avatar_split_clause,[],[f444,f470,f466,f462])).
% 5.52/1.12  fof(f444,plain,(
% 5.52/1.12    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 5.52/1.12    inference(resolution,[],[f101,f76])).
% 5.52/1.12  fof(f101,plain,(
% 5.52/1.12    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 5.52/1.12    inference(cnf_transformation,[],[f56])).
% 5.52/1.12  fof(f56,plain,(
% 5.52/1.12    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 5.52/1.12    inference(flattening,[],[f55])).
% 5.52/1.12  fof(f55,plain,(
% 5.52/1.12    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 5.52/1.12    inference(ennf_transformation,[],[f27])).
% 5.52/1.12  fof(f27,axiom,(
% 5.52/1.12    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 5.52/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 5.52/1.12  fof(f460,plain,(
% 5.52/1.12    spl3_11 | ~spl3_12 | ~spl3_13),
% 5.52/1.12    inference(avatar_split_clause,[],[f443,f457,f453,f449])).
% 5.52/1.12  fof(f443,plain,(
% 5.52/1.12    ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | sK0 = k1_relset_1(sK0,sK0,sK2)),
% 5.52/1.12    inference(resolution,[],[f101,f70])).
% 5.52/1.12  fof(f151,plain,(
% 5.52/1.12    spl3_2),
% 5.52/1.12    inference(avatar_contradiction_clause,[],[f148])).
% 5.52/1.12  fof(f148,plain,(
% 5.52/1.12    $false | spl3_2),
% 5.52/1.12    inference(unit_resulting_resolution,[],[f95,f141])).
% 5.52/1.12  fof(f141,plain,(
% 5.52/1.12    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_2),
% 5.52/1.12    inference(avatar_component_clause,[],[f139])).
% 5.52/1.12  fof(f139,plain,(
% 5.52/1.12    spl3_2 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 5.52/1.12    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 5.52/1.12  fof(f95,plain,(
% 5.52/1.12    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 5.52/1.12    inference(cnf_transformation,[],[f5])).
% 5.52/1.12  fof(f5,axiom,(
% 5.52/1.12    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 5.52/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 5.52/1.12  fof(f147,plain,(
% 5.52/1.12    spl3_3 | ~spl3_2),
% 5.52/1.12    inference(avatar_split_clause,[],[f132,f139,f144])).
% 5.52/1.12  fof(f132,plain,(
% 5.52/1.12    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1)),
% 5.52/1.12    inference(resolution,[],[f82,f76])).
% 5.52/1.12  fof(f82,plain,(
% 5.52/1.12    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 5.52/1.12    inference(cnf_transformation,[],[f34])).
% 5.52/1.12  fof(f34,plain,(
% 5.52/1.12    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 5.52/1.12    inference(ennf_transformation,[],[f3])).
% 5.52/1.12  fof(f3,axiom,(
% 5.52/1.12    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 5.52/1.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 5.52/1.12  fof(f142,plain,(
% 5.52/1.12    spl3_1 | ~spl3_2),
% 5.52/1.12    inference(avatar_split_clause,[],[f131,f139,f135])).
% 5.52/1.12  fof(f131,plain,(
% 5.52/1.12    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK2)),
% 5.52/1.12    inference(resolution,[],[f82,f70])).
% 5.52/1.12  % SZS output end Proof for theBenchmark
% 5.52/1.12  % (27216)------------------------------
% 5.52/1.12  % (27216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.52/1.12  % (27216)Termination reason: Refutation
% 5.52/1.12  
% 5.52/1.12  % (27216)Memory used [KB]: 13432
% 5.52/1.12  % (27216)Time elapsed: 0.681 s
% 5.52/1.12  % (27216)------------------------------
% 5.52/1.12  % (27216)------------------------------
% 5.52/1.13  % (27199)Success in time 0.76 s
%------------------------------------------------------------------------------
