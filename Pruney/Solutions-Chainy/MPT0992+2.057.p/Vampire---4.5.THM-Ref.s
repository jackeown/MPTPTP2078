%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:18 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 398 expanded)
%              Number of leaves         :   33 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  430 (1650 expanded)
%              Number of equality atoms :   80 ( 371 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f146,f168,f172,f194,f237,f359,f1683,f1705,f1770,f2550,f2553,f2755,f2765,f3203,f3213,f3398])).

fof(f3398,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f3386])).

fof(f3386,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f3272,f3306])).

fof(f3306,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f3305,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_12 ),
    inference(resolution,[],[f193,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f193,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_12
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f3305,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(forward_demodulation,[],[f3304,f399])).

fof(f399,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_3 ),
    inference(resolution,[],[f375,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f375,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f367,f81])).

fof(f81,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f367,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f124,f111])).

fof(f111,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f124,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f45,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f3304,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(forward_demodulation,[],[f2871,f382])).

fof(f382,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3 ),
    inference(resolution,[],[f363,f50])).

fof(f363,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f46,f111])).

fof(f46,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f2871,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | ~ spl4_4
    | spl4_6 ),
    inference(backward_demodulation,[],[f756,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f756,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_6 ),
    inference(backward_demodulation,[],[f141,f127])).

fof(f127,plain,(
    ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_subsumption,[],[f43,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f45,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f141,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_6
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f3272,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f3233,f399])).

fof(f3233,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f3214,f114])).

fof(f3214,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f44,f111])).

fof(f44,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f3213,plain,(
    spl4_47 ),
    inference(avatar_split_clause,[],[f3201,f2762])).

fof(f2762,plain,
    ( spl4_47
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f3201,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f90,f61])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f46,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3203,plain,
    ( ~ spl4_45
    | spl4_6 ),
    inference(avatar_split_clause,[],[f756,f139,f2748])).

fof(f2748,plain,
    ( spl4_45
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f2765,plain,
    ( ~ spl4_10
    | ~ spl4_47
    | ~ spl4_17
    | spl4_46 ),
    inference(avatar_split_clause,[],[f2759,f2752,f356,f2762,f161])).

fof(f161,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f356,plain,
    ( spl4_17
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f2752,plain,
    ( spl4_46
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f2759,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_17
    | spl4_46 ),
    inference(forward_demodulation,[],[f2758,f683])).

fof(f683,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f117,f358])).

fof(f358,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f356])).

fof(f117,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2758,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_46 ),
    inference(trivial_inequality_removal,[],[f2756])).

fof(f2756,plain,
    ( sK2 != sK2
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_46 ),
    inference(superposition,[],[f2754,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2754,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_46 ),
    inference(avatar_component_clause,[],[f2752])).

fof(f2755,plain,
    ( spl4_45
    | spl4_4
    | ~ spl4_46
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f2718,f135,f2752,f113,f2748])).

fof(f135,plain,
    ( spl4_5
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2718,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f2565,f2563])).

fof(f2563,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_5 ),
    inference(resolution,[],[f2556,f66])).

fof(f2556,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f136,f127])).

fof(f136,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f2565,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f2556,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f2553,plain,(
    spl4_39 ),
    inference(avatar_contradiction_clause,[],[f2551])).

fof(f2551,plain,
    ( $false
    | spl4_39 ),
    inference(resolution,[],[f2549,f986])).

fof(f986,plain,(
    ! [X1] : v5_relat_1(k7_relat_1(sK3,X1),sK1) ),
    inference(resolution,[],[f946,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f946,plain,(
    ! [X2] : m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f129,f127])).

fof(f129,plain,(
    ! [X2] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f43,f123])).

fof(f123,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK3)
      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(resolution,[],[f45,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f2549,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f2547])).

fof(f2547,plain,
    ( spl4_39
  <=> v5_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f2550,plain,
    ( ~ spl4_39
    | ~ spl4_29
    | spl4_27 ),
    inference(avatar_split_clause,[],[f1745,f1672,f1680,f2547])).

fof(f1680,plain,
    ( spl4_29
  <=> v1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f1672,plain,
    ( spl4_27
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1745,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_27 ),
    inference(resolution,[],[f1674,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1674,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f1672])).

fof(f1770,plain,
    ( ~ spl4_10
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f1767])).

fof(f1767,plain,
    ( $false
    | ~ spl4_10
    | spl4_28 ),
    inference(resolution,[],[f1678,f176])).

fof(f176,plain,
    ( ! [X2] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X2)),X2)
    | ~ spl4_10 ),
    inference(resolution,[],[f163,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f163,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1678,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f1676])).

fof(f1676,plain,
    ( spl4_28
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1705,plain,
    ( ~ spl4_10
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f1702])).

fof(f1702,plain,
    ( $false
    | ~ spl4_10
    | spl4_29 ),
    inference(resolution,[],[f1682,f175])).

fof(f175,plain,
    ( ! [X1] : v1_relat_1(k7_relat_1(sK3,X1))
    | ~ spl4_10 ),
    inference(resolution,[],[f163,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f1682,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f1680])).

fof(f1683,plain,
    ( ~ spl4_27
    | ~ spl4_28
    | ~ spl4_29
    | spl4_5 ),
    inference(avatar_split_clause,[],[f787,f135,f1680,f1676,f1672])).

fof(f787,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_5 ),
    inference(resolution,[],[f755,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f755,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_5 ),
    inference(backward_demodulation,[],[f137,f127])).

fof(f137,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f359,plain,
    ( spl4_4
    | spl4_17 ),
    inference(avatar_split_clause,[],[f94,f356,f113])).

fof(f94,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f45,f93])).

fof(f93,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f44,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f237,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f145,f128])).

fof(f128,plain,(
    ! [X1] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ),
    inference(global_subsumption,[],[f43,f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1)) ) ),
    inference(resolution,[],[f45,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f145,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_7
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f194,plain,
    ( ~ spl4_10
    | spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f187,f161,f191,f161])).

fof(f187,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(superposition,[],[f175,f48])).

fof(f172,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f167,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f167,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_11
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f168,plain,
    ( spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f125,f165,f161])).

fof(f125,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f146,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f41,f143,f139,f135])).

fof(f41,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f42,f113,f109])).

fof(f42,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:57 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.48  % (17511)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (17518)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (17504)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (17503)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (17500)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (17510)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (17519)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (17515)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (17501)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (17508)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (17520)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (17522)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (17509)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (17512)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (17506)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (17502)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (17507)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (17521)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (17513)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (17523)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (17499)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (17524)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (17517)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (17516)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (17514)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.56  % (17505)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 2.07/0.64  % (17519)Refutation found. Thanks to Tanya!
% 2.07/0.64  % SZS status Theorem for theBenchmark
% 2.07/0.64  % SZS output start Proof for theBenchmark
% 2.07/0.64  fof(f3403,plain,(
% 2.07/0.64    $false),
% 2.07/0.64    inference(avatar_sat_refutation,[],[f116,f146,f168,f172,f194,f237,f359,f1683,f1705,f1770,f2550,f2553,f2755,f2765,f3203,f3213,f3398])).
% 2.07/0.64  fof(f3398,plain,(
% 2.07/0.64    ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_12),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f3386])).
% 2.07/0.64  fof(f3386,plain,(
% 2.07/0.64    $false | (~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_12)),
% 2.07/0.64    inference(subsumption_resolution,[],[f3272,f3306])).
% 2.07/0.64  fof(f3306,plain,(
% 2.07/0.64    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_12)),
% 2.07/0.64    inference(forward_demodulation,[],[f3305,f195])).
% 2.07/0.64  fof(f195,plain,(
% 2.07/0.64    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl4_12),
% 2.07/0.64    inference(resolution,[],[f193,f48])).
% 2.07/0.64  fof(f48,plain,(
% 2.07/0.64    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f23])).
% 2.07/0.64  fof(f23,plain,(
% 2.07/0.64    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(ennf_transformation,[],[f10])).
% 2.07/0.64  fof(f10,axiom,(
% 2.07/0.64    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 2.07/0.64  fof(f193,plain,(
% 2.07/0.64    v1_relat_1(k1_xboole_0) | ~spl4_12),
% 2.07/0.64    inference(avatar_component_clause,[],[f191])).
% 2.07/0.64  fof(f191,plain,(
% 2.07/0.64    spl4_12 <=> v1_relat_1(k1_xboole_0)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.07/0.64  fof(f3305,plain,(
% 2.07/0.64    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | spl4_6)),
% 2.07/0.64    inference(forward_demodulation,[],[f3304,f399])).
% 2.07/0.64  fof(f399,plain,(
% 2.07/0.64    k1_xboole_0 = sK3 | ~spl4_3),
% 2.07/0.64    inference(resolution,[],[f375,f50])).
% 2.07/0.64  fof(f50,plain,(
% 2.07/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f25])).
% 2.07/0.64  fof(f25,plain,(
% 2.07/0.64    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.07/0.64    inference(ennf_transformation,[],[f3])).
% 2.07/0.64  fof(f3,axiom,(
% 2.07/0.64    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.07/0.64  fof(f375,plain,(
% 2.07/0.64    r1_tarski(sK3,k1_xboole_0) | ~spl4_3),
% 2.07/0.64    inference(forward_demodulation,[],[f367,f81])).
% 2.07/0.64  fof(f81,plain,(
% 2.07/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.07/0.64    inference(equality_resolution,[],[f63])).
% 2.07/0.64  fof(f63,plain,(
% 2.07/0.64    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f4])).
% 2.07/0.64  fof(f4,axiom,(
% 2.07/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.07/0.64  fof(f367,plain,(
% 2.07/0.64    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_3),
% 2.07/0.64    inference(backward_demodulation,[],[f124,f111])).
% 2.07/0.64  fof(f111,plain,(
% 2.07/0.64    k1_xboole_0 = sK0 | ~spl4_3),
% 2.07/0.64    inference(avatar_component_clause,[],[f109])).
% 2.07/0.64  fof(f109,plain,(
% 2.07/0.64    spl4_3 <=> k1_xboole_0 = sK0),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.07/0.64  fof(f124,plain,(
% 2.07/0.64    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 2.07/0.64    inference(resolution,[],[f45,f61])).
% 2.07/0.64  fof(f61,plain,(
% 2.07/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f5])).
% 2.07/0.64  fof(f5,axiom,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.07/0.64  fof(f45,plain,(
% 2.07/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f22,plain,(
% 2.07/0.64    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.07/0.64    inference(flattening,[],[f21])).
% 2.07/0.64  fof(f21,plain,(
% 2.07/0.64    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.07/0.64    inference(ennf_transformation,[],[f20])).
% 2.07/0.64  fof(f20,negated_conjecture,(
% 2.07/0.64    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.07/0.64    inference(negated_conjecture,[],[f19])).
% 2.07/0.64  fof(f19,conjecture,(
% 2.07/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 2.07/0.64  fof(f3304,plain,(
% 2.07/0.64    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | spl4_6)),
% 2.07/0.64    inference(forward_demodulation,[],[f2871,f382])).
% 2.07/0.64  fof(f382,plain,(
% 2.07/0.64    k1_xboole_0 = sK2 | ~spl4_3),
% 2.07/0.64    inference(resolution,[],[f363,f50])).
% 2.07/0.64  fof(f363,plain,(
% 2.07/0.64    r1_tarski(sK2,k1_xboole_0) | ~spl4_3),
% 2.07/0.64    inference(backward_demodulation,[],[f46,f111])).
% 2.07/0.64  fof(f46,plain,(
% 2.07/0.64    r1_tarski(sK2,sK0)),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f2871,plain,(
% 2.07/0.64    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (~spl4_4 | spl4_6)),
% 2.07/0.64    inference(backward_demodulation,[],[f756,f114])).
% 2.07/0.64  fof(f114,plain,(
% 2.07/0.64    k1_xboole_0 = sK1 | ~spl4_4),
% 2.07/0.64    inference(avatar_component_clause,[],[f113])).
% 2.07/0.64  fof(f113,plain,(
% 2.07/0.64    spl4_4 <=> k1_xboole_0 = sK1),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.07/0.64  fof(f756,plain,(
% 2.07/0.64    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_6),
% 2.07/0.64    inference(backward_demodulation,[],[f141,f127])).
% 2.07/0.64  fof(f127,plain,(
% 2.07/0.64    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 2.07/0.64    inference(global_subsumption,[],[f43,f121])).
% 2.07/0.64  fof(f121,plain,(
% 2.07/0.64    ( ! [X0] : (~v1_funct_1(sK3) | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 2.07/0.64    inference(resolution,[],[f45,f75])).
% 2.07/0.64  fof(f75,plain,(
% 2.07/0.64    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f38])).
% 2.07/0.64  fof(f38,plain,(
% 2.07/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.07/0.64    inference(flattening,[],[f37])).
% 2.07/0.64  fof(f37,plain,(
% 2.07/0.64    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.07/0.64    inference(ennf_transformation,[],[f18])).
% 2.07/0.64  fof(f18,axiom,(
% 2.07/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.07/0.64  fof(f43,plain,(
% 2.07/0.64    v1_funct_1(sK3)),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f141,plain,(
% 2.07/0.64    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_6),
% 2.07/0.64    inference(avatar_component_clause,[],[f139])).
% 2.07/0.64  fof(f139,plain,(
% 2.07/0.64    spl4_6 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.07/0.64  fof(f3272,plain,(
% 2.07/0.64    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4)),
% 2.07/0.64    inference(forward_demodulation,[],[f3233,f399])).
% 2.07/0.64  fof(f3233,plain,(
% 2.07/0.64    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4)),
% 2.07/0.64    inference(forward_demodulation,[],[f3214,f114])).
% 2.07/0.64  fof(f3214,plain,(
% 2.07/0.64    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_3),
% 2.07/0.64    inference(backward_demodulation,[],[f44,f111])).
% 2.07/0.64  fof(f44,plain,(
% 2.07/0.64    v1_funct_2(sK3,sK0,sK1)),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f3213,plain,(
% 2.07/0.64    spl4_47),
% 2.07/0.64    inference(avatar_split_clause,[],[f3201,f2762])).
% 2.07/0.64  fof(f2762,plain,(
% 2.07/0.64    spl4_47 <=> r1_tarski(sK2,sK0)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 2.07/0.64  fof(f3201,plain,(
% 2.07/0.64    r1_tarski(sK2,sK0)),
% 2.07/0.64    inference(resolution,[],[f90,f61])).
% 2.07/0.64  fof(f90,plain,(
% 2.07/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.07/0.64    inference(resolution,[],[f46,f60])).
% 2.07/0.64  fof(f60,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f5])).
% 2.07/0.64  fof(f3203,plain,(
% 2.07/0.64    ~spl4_45 | spl4_6),
% 2.07/0.64    inference(avatar_split_clause,[],[f756,f139,f2748])).
% 2.07/0.64  fof(f2748,plain,(
% 2.07/0.64    spl4_45 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.07/0.64  fof(f2765,plain,(
% 2.07/0.64    ~spl4_10 | ~spl4_47 | ~spl4_17 | spl4_46),
% 2.07/0.64    inference(avatar_split_clause,[],[f2759,f2752,f356,f2762,f161])).
% 2.07/0.64  fof(f161,plain,(
% 2.07/0.64    spl4_10 <=> v1_relat_1(sK3)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.07/0.64  fof(f356,plain,(
% 2.07/0.64    spl4_17 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.07/0.64  fof(f2752,plain,(
% 2.07/0.64    spl4_46 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.07/0.64  fof(f2759,plain,(
% 2.07/0.64    ~r1_tarski(sK2,sK0) | ~v1_relat_1(sK3) | (~spl4_17 | spl4_46)),
% 2.07/0.64    inference(forward_demodulation,[],[f2758,f683])).
% 2.07/0.64  fof(f683,plain,(
% 2.07/0.64    sK0 = k1_relat_1(sK3) | ~spl4_17),
% 2.07/0.64    inference(backward_demodulation,[],[f117,f358])).
% 2.07/0.64  fof(f358,plain,(
% 2.07/0.64    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_17),
% 2.07/0.64    inference(avatar_component_clause,[],[f356])).
% 2.07/0.64  fof(f117,plain,(
% 2.07/0.64    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 2.07/0.64    inference(resolution,[],[f45,f66])).
% 2.07/0.64  fof(f66,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f33])).
% 2.07/0.64  fof(f33,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.64    inference(ennf_transformation,[],[f14])).
% 2.07/0.64  fof(f14,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.07/0.64  fof(f2758,plain,(
% 2.07/0.64    ~v1_relat_1(sK3) | ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_46),
% 2.07/0.64    inference(trivial_inequality_removal,[],[f2756])).
% 2.07/0.64  fof(f2756,plain,(
% 2.07/0.64    sK2 != sK2 | ~v1_relat_1(sK3) | ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_46),
% 2.07/0.64    inference(superposition,[],[f2754,f54])).
% 2.07/0.64  fof(f54,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 2.07/0.64    inference(cnf_transformation,[],[f29])).
% 2.07/0.64  fof(f29,plain,(
% 2.07/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(flattening,[],[f28])).
% 2.07/0.64  fof(f28,plain,(
% 2.07/0.64    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f12])).
% 2.07/0.64  fof(f12,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.07/0.64  fof(f2754,plain,(
% 2.07/0.64    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | spl4_46),
% 2.07/0.64    inference(avatar_component_clause,[],[f2752])).
% 2.07/0.64  fof(f2755,plain,(
% 2.07/0.64    spl4_45 | spl4_4 | ~spl4_46 | ~spl4_5),
% 2.07/0.64    inference(avatar_split_clause,[],[f2718,f135,f2752,f113,f2748])).
% 2.07/0.64  fof(f135,plain,(
% 2.07/0.64    spl4_5 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.07/0.64  fof(f2718,plain,(
% 2.07/0.64    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_5),
% 2.07/0.64    inference(forward_demodulation,[],[f2565,f2563])).
% 2.07/0.64  fof(f2563,plain,(
% 2.07/0.64    k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_5),
% 2.07/0.64    inference(resolution,[],[f2556,f66])).
% 2.07/0.64  fof(f2556,plain,(
% 2.07/0.64    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_5),
% 2.07/0.64    inference(forward_demodulation,[],[f136,f127])).
% 2.07/0.64  fof(f136,plain,(
% 2.07/0.64    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_5),
% 2.07/0.64    inference(avatar_component_clause,[],[f135])).
% 2.07/0.64  fof(f2565,plain,(
% 2.07/0.64    k1_xboole_0 = sK1 | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_5),
% 2.07/0.64    inference(resolution,[],[f2556,f73])).
% 2.07/0.64  fof(f73,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f36])).
% 2.07/0.64  fof(f36,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.64    inference(flattening,[],[f35])).
% 2.07/0.64  fof(f35,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.64    inference(ennf_transformation,[],[f16])).
% 2.07/0.64  fof(f16,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.07/0.64  fof(f2553,plain,(
% 2.07/0.64    spl4_39),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f2551])).
% 2.07/0.64  fof(f2551,plain,(
% 2.07/0.64    $false | spl4_39),
% 2.07/0.64    inference(resolution,[],[f2549,f986])).
% 2.07/0.64  fof(f986,plain,(
% 2.07/0.64    ( ! [X1] : (v5_relat_1(k7_relat_1(sK3,X1),sK1)) )),
% 2.07/0.64    inference(resolution,[],[f946,f68])).
% 2.07/0.64  fof(f68,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f34])).
% 2.07/0.64  fof(f34,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.64    inference(ennf_transformation,[],[f13])).
% 2.07/0.64  fof(f13,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.07/0.64  fof(f946,plain,(
% 2.07/0.64    ( ! [X2] : (m1_subset_1(k7_relat_1(sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 2.07/0.64    inference(forward_demodulation,[],[f129,f127])).
% 2.07/0.64  fof(f129,plain,(
% 2.07/0.64    ( ! [X2] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 2.07/0.64    inference(global_subsumption,[],[f43,f123])).
% 2.07/0.64  fof(f123,plain,(
% 2.07/0.64    ( ! [X2] : (~v1_funct_1(sK3) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 2.07/0.64    inference(resolution,[],[f45,f77])).
% 2.07/0.64  fof(f77,plain,(
% 2.07/0.64    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f40])).
% 2.07/0.64  fof(f40,plain,(
% 2.07/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.07/0.64    inference(flattening,[],[f39])).
% 2.07/0.64  fof(f39,plain,(
% 2.07/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.07/0.64    inference(ennf_transformation,[],[f17])).
% 2.07/0.64  fof(f17,axiom,(
% 2.07/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 2.07/0.64  fof(f2549,plain,(
% 2.07/0.64    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_39),
% 2.07/0.64    inference(avatar_component_clause,[],[f2547])).
% 2.07/0.64  fof(f2547,plain,(
% 2.07/0.64    spl4_39 <=> v5_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.07/0.64  fof(f2550,plain,(
% 2.07/0.64    ~spl4_39 | ~spl4_29 | spl4_27),
% 2.07/0.64    inference(avatar_split_clause,[],[f1745,f1672,f1680,f2547])).
% 2.07/0.64  fof(f1680,plain,(
% 2.07/0.64    spl4_29 <=> v1_relat_1(k7_relat_1(sK3,sK2))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.07/0.64  fof(f1672,plain,(
% 2.07/0.64    spl4_27 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.07/0.64  fof(f1745,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_27),
% 2.07/0.64    inference(resolution,[],[f1674,f56])).
% 2.07/0.64  fof(f56,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f30])).
% 2.07/0.64  fof(f30,plain,(
% 2.07/0.64    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f7])).
% 2.07/0.64  fof(f7,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.07/0.64  fof(f1674,plain,(
% 2.07/0.64    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl4_27),
% 2.07/0.64    inference(avatar_component_clause,[],[f1672])).
% 2.07/0.64  fof(f1770,plain,(
% 2.07/0.64    ~spl4_10 | spl4_28),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f1767])).
% 2.07/0.64  fof(f1767,plain,(
% 2.07/0.64    $false | (~spl4_10 | spl4_28)),
% 2.07/0.64    inference(resolution,[],[f1678,f176])).
% 2.07/0.64  fof(f176,plain,(
% 2.07/0.64    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X2)),X2)) ) | ~spl4_10),
% 2.07/0.64    inference(resolution,[],[f163,f53])).
% 2.07/0.64  fof(f53,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f27])).
% 2.07/0.64  fof(f27,plain,(
% 2.07/0.64    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.07/0.64    inference(ennf_transformation,[],[f11])).
% 2.07/0.64  fof(f11,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 2.07/0.64  fof(f163,plain,(
% 2.07/0.64    v1_relat_1(sK3) | ~spl4_10),
% 2.07/0.64    inference(avatar_component_clause,[],[f161])).
% 2.07/0.64  fof(f1678,plain,(
% 2.07/0.64    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_28),
% 2.07/0.64    inference(avatar_component_clause,[],[f1676])).
% 2.07/0.64  fof(f1676,plain,(
% 2.07/0.64    spl4_28 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.07/0.64  fof(f1705,plain,(
% 2.07/0.64    ~spl4_10 | spl4_29),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f1702])).
% 2.07/0.64  fof(f1702,plain,(
% 2.07/0.64    $false | (~spl4_10 | spl4_29)),
% 2.07/0.64    inference(resolution,[],[f1682,f175])).
% 2.07/0.64  fof(f175,plain,(
% 2.07/0.64    ( ! [X1] : (v1_relat_1(k7_relat_1(sK3,X1))) ) | ~spl4_10),
% 2.07/0.64    inference(resolution,[],[f163,f52])).
% 2.07/0.64  fof(f52,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f26])).
% 2.07/0.64  fof(f26,plain,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(ennf_transformation,[],[f8])).
% 2.07/0.64  fof(f8,axiom,(
% 2.07/0.64    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.07/0.64  fof(f1682,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_29),
% 2.07/0.64    inference(avatar_component_clause,[],[f1680])).
% 2.07/0.64  fof(f1683,plain,(
% 2.07/0.64    ~spl4_27 | ~spl4_28 | ~spl4_29 | spl4_5),
% 2.07/0.64    inference(avatar_split_clause,[],[f787,f135,f1680,f1676,f1672])).
% 2.07/0.64  fof(f787,plain,(
% 2.07/0.64    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl4_5),
% 2.07/0.64    inference(resolution,[],[f755,f65])).
% 2.07/0.64  fof(f65,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f32])).
% 2.07/0.64  fof(f32,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.07/0.64    inference(flattening,[],[f31])).
% 2.07/0.64  fof(f31,plain,(
% 2.07/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.07/0.64    inference(ennf_transformation,[],[f15])).
% 2.07/0.64  fof(f15,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 2.07/0.64  fof(f755,plain,(
% 2.07/0.64    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_5),
% 2.07/0.64    inference(backward_demodulation,[],[f137,f127])).
% 2.07/0.64  fof(f137,plain,(
% 2.07/0.64    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_5),
% 2.07/0.64    inference(avatar_component_clause,[],[f135])).
% 2.07/0.64  fof(f359,plain,(
% 2.07/0.64    spl4_4 | spl4_17),
% 2.07/0.64    inference(avatar_split_clause,[],[f94,f356,f113])).
% 2.07/0.64  fof(f94,plain,(
% 2.07/0.64    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1),
% 2.07/0.64    inference(global_subsumption,[],[f45,f93])).
% 2.07/0.64  fof(f93,plain,(
% 2.07/0.64    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.07/0.64    inference(resolution,[],[f44,f74])).
% 2.07/0.64  fof(f74,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f36])).
% 2.07/0.64  fof(f237,plain,(
% 2.07/0.64    spl4_7),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f232])).
% 2.07/0.64  fof(f232,plain,(
% 2.07/0.64    $false | spl4_7),
% 2.07/0.64    inference(subsumption_resolution,[],[f145,f128])).
% 2.07/0.64  fof(f128,plain,(
% 2.07/0.64    ( ! [X1] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 2.07/0.64    inference(global_subsumption,[],[f43,f122])).
% 2.07/0.64  fof(f122,plain,(
% 2.07/0.64    ( ! [X1] : (~v1_funct_1(sK3) | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))) )),
% 2.07/0.64    inference(resolution,[],[f45,f76])).
% 2.07/0.64  fof(f76,plain,(
% 2.07/0.64    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f40])).
% 2.07/0.64  fof(f145,plain,(
% 2.07/0.64    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_7),
% 2.07/0.64    inference(avatar_component_clause,[],[f143])).
% 2.07/0.64  fof(f143,plain,(
% 2.07/0.64    spl4_7 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.07/0.64  fof(f194,plain,(
% 2.07/0.64    ~spl4_10 | spl4_12 | ~spl4_10),
% 2.07/0.64    inference(avatar_split_clause,[],[f187,f161,f191,f161])).
% 2.07/0.64  fof(f187,plain,(
% 2.07/0.64    v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK3) | ~spl4_10),
% 2.07/0.64    inference(superposition,[],[f175,f48])).
% 2.07/0.64  fof(f172,plain,(
% 2.07/0.64    spl4_11),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f170])).
% 2.07/0.64  fof(f170,plain,(
% 2.07/0.64    $false | spl4_11),
% 2.07/0.64    inference(resolution,[],[f167,f51])).
% 2.07/0.64  fof(f51,plain,(
% 2.07/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f9])).
% 2.07/0.64  fof(f9,axiom,(
% 2.07/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.07/0.64  fof(f167,plain,(
% 2.07/0.64    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_11),
% 2.07/0.64    inference(avatar_component_clause,[],[f165])).
% 2.07/0.64  fof(f165,plain,(
% 2.07/0.64    spl4_11 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.07/0.64  fof(f168,plain,(
% 2.07/0.64    spl4_10 | ~spl4_11),
% 2.07/0.64    inference(avatar_split_clause,[],[f125,f165,f161])).
% 2.07/0.64  fof(f125,plain,(
% 2.07/0.64    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 2.07/0.64    inference(resolution,[],[f45,f49])).
% 2.07/0.64  fof(f49,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f24])).
% 2.07/0.64  fof(f24,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.07/0.64    inference(ennf_transformation,[],[f6])).
% 2.07/0.64  fof(f6,axiom,(
% 2.07/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.07/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.07/0.64  fof(f146,plain,(
% 2.07/0.64    ~spl4_5 | ~spl4_6 | ~spl4_7),
% 2.07/0.64    inference(avatar_split_clause,[],[f41,f143,f139,f135])).
% 2.07/0.64  fof(f41,plain,(
% 2.07/0.64    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f116,plain,(
% 2.07/0.64    spl4_3 | ~spl4_4),
% 2.07/0.64    inference(avatar_split_clause,[],[f42,f113,f109])).
% 2.07/0.64  fof(f42,plain,(
% 2.07/0.64    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  % SZS output end Proof for theBenchmark
% 2.07/0.64  % (17519)------------------------------
% 2.07/0.64  % (17519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (17519)Termination reason: Refutation
% 2.07/0.64  
% 2.07/0.64  % (17519)Memory used [KB]: 11897
% 2.07/0.64  % (17519)Time elapsed: 0.227 s
% 2.07/0.64  % (17519)------------------------------
% 2.07/0.64  % (17519)------------------------------
% 2.07/0.64  % (17498)Success in time 0.282 s
%------------------------------------------------------------------------------
