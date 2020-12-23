%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 685 expanded)
%              Number of leaves         :   34 ( 191 expanded)
%              Depth                    :   21
%              Number of atoms          :  645 (3422 expanded)
%              Number of equality atoms :  113 ( 767 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f167,f196,f202,f277,f814,f1422,f1657,f1672,f1855,f1867,f1920,f1921,f3325,f3328,f3354])).

fof(f3354,plain,
    ( spl4_2
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f3353])).

fof(f3353,plain,
    ( $false
    | spl4_2
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f3186,f3351])).

fof(f3351,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f106,f163])).

fof(f163,plain,(
    ! [X2] : k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(subsumption_resolution,[],[f154,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f154,plain,(
    ! [X2] :
      ( k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f55,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3186,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(resolution,[],[f3161,f269])).

fof(f269,plain,
    ( ! [X4] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),sK1)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f265,f184])).

fof(f184,plain,
    ( ! [X7] : v1_relat_1(k7_relat_1(sK3,X7))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_12
  <=> ! [X7] : v1_relat_1(k7_relat_1(sK3,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f265,plain,
    ( ! [X4] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),sK1)
        | ~ v1_relat_1(k7_relat_1(sK3,X4)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f190,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f190,plain,
    ( ! [X1] : v5_relat_1(k7_relat_1(sK3,X1),sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f187,f128])).

fof(f128,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f187,plain,(
    ! [X1] :
      ( v5_relat_1(k7_relat_1(sK3,X1),sK1)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f159,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v5_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

fof(f159,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f55,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f3161,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f3160,f163])).

fof(f3160,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f3159,f2774])).

fof(f2774,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(resolution,[],[f1958,f56])).

fof(f56,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f1958,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2 )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f1952,f128])).

fof(f1952,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_relat_1(k7_relat_1(sK3,X2)) = X2
        | ~ v1_relat_1(sK3) )
    | ~ spl4_10 ),
    inference(superposition,[],[f74,f1946])).

fof(f1946,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f1942,f55])).

fof(f1942,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(superposition,[],[f150,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f150,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f3159,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) )
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f227,f163])).

fof(f227,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl4_14
  <=> ! [X0] :
        ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f3328,plain,
    ( ~ spl4_12
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f3327])).

fof(f3327,plain,
    ( $false
    | ~ spl4_12
    | spl4_13 ),
    inference(subsumption_resolution,[],[f3326,f184])).

fof(f3326,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_13 ),
    inference(forward_demodulation,[],[f224,f163])).

fof(f224,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl4_13
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f3325,plain,
    ( spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f3324])).

fof(f3324,plain,
    ( $false
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f3321,f274])).

fof(f274,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f273,f53])).

fof(f273,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f272,f55])).

fof(f272,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(superposition,[],[f110,f61])).

fof(f110,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3321,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(resolution,[],[f3296,f269])).

fof(f3296,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f3295,f163])).

fof(f3295,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f3294,f2774])).

fof(f3294,plain,
    ( ! [X1] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1) )
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f231,f163])).

fof(f231,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl4_15
  <=> ! [X1] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1921,plain,
    ( ~ spl4_13
    | spl4_15
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f1915,f100,f230,f222])).

fof(f100,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1915,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1)))
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f101,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f101,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1920,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f1914,f100,f226,f222])).

fof(f1914,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0)
        | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f101,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1867,plain,
    ( spl4_11
    | spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1863,f127,f183,f180])).

fof(f180,plain,
    ( spl4_11
  <=> ! [X8] : ~ v5_relat_1(sK3,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1863,plain,
    ( ! [X8,X7] :
        ( v1_relat_1(k7_relat_1(sK3,X7))
        | ~ v5_relat_1(sK3,X8) )
    | ~ spl4_6 ),
    inference(resolution,[],[f128,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1855,plain,
    ( ~ spl4_9
    | spl4_10
    | spl4_4 ),
    inference(avatar_split_clause,[],[f1854,f113,f148,f144])).

fof(f144,plain,
    ( spl4_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f113,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1854,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f1853,f115])).

fof(f115,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f1853,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1672,plain,
    ( spl4_3
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f1671])).

fof(f1671,plain,
    ( $false
    | spl4_3
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1670,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1670,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1669,f836])).

fof(f836,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f821,f76])).

fof(f76,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f821,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl4_25 ),
    inference(resolution,[],[f695,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f695,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_25
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1669,plain,
    ( ~ m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1668,f470])).

fof(f470,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl4_21
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1668,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_3
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1667,f98])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1667,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl4_3
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f274,f1412])).

fof(f1412,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(resolution,[],[f1189,f295])).

fof(f295,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f56,f119])).

fof(f119,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1189,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k1_xboole_0)
        | k1_xboole_0 = X4 )
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1188,f76])).

fof(f1188,plain,
    ( ! [X4] :
        ( k1_xboole_0 = X4
        | ~ r1_tarski(X4,k1_relat_1(k1_xboole_0)) )
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1187,f76])).

fof(f1187,plain,
    ( ! [X4] :
        ( k1_relat_1(k1_xboole_0) = X4
        | ~ r1_tarski(X4,k1_relat_1(k1_xboole_0)) )
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1182,f695])).

fof(f1182,plain,
    ( ! [X4] :
        ( k1_relat_1(k1_xboole_0) = X4
        | ~ r1_tarski(X4,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_25 ),
    inference(superposition,[],[f74,f1133])).

fof(f1133,plain,
    ( ! [X2] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1132,f695])).

fof(f1132,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1128,f79])).

fof(f79,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1128,plain,
    ( ! [X2] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)
        | ~ r1_tarski(k1_xboole_0,X2)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_25 ),
    inference(superposition,[],[f69,f836])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f1657,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f1656])).

fof(f1656,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1655,f1579])).

fof(f1579,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f760,f470])).

fof(f760,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f54,f119])).

fof(f1655,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1654,f836])).

fof(f1654,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1653,f662])).

fof(f662,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f53,f470])).

fof(f1653,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1633,f78])).

fof(f1633,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(superposition,[],[f1583,f61])).

fof(f1583,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f1430,f470])).

fof(f1430,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f756,f1412])).

fof(f756,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f106,f119])).

fof(f1422,plain,
    ( ~ spl4_5
    | spl4_21
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f1421])).

fof(f1421,plain,
    ( $false
    | ~ spl4_5
    | spl4_21
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f1413,f469])).

fof(f469,plain,
    ( k1_xboole_0 != sK3
    | spl4_21 ),
    inference(avatar_component_clause,[],[f468])).

fof(f1413,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5
    | ~ spl4_25 ),
    inference(resolution,[],[f1189,f755])).

fof(f755,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f754,f98])).

fof(f754,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f160,f119])).

fof(f160,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f55,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f814,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f813])).

fof(f813,plain,
    ( $false
    | spl4_25 ),
    inference(subsumption_resolution,[],[f805,f78])).

fof(f805,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_25 ),
    inference(resolution,[],[f696,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f696,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f694])).

fof(f277,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f146,f55])).

fof(f146,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f202,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl4_11 ),
    inference(resolution,[],[f181,f159])).

fof(f181,plain,
    ( ! [X8] : ~ v5_relat_1(sK3,X8)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f196,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f194,f53])).

fof(f194,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f192,f55])).

fof(f192,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f102,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f102,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f167,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f158,f129])).

fof(f129,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f158,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f88])).

fof(f120,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f57,f117,f113])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f108,f104,f100])).

fof(f58,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31875)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.46  % (31869)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (31863)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (31856)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (31865)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (31860)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (31876)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (31876)Refutation not found, incomplete strategy% (31876)------------------------------
% 0.20/0.49  % (31876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (31876)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (31876)Memory used [KB]: 10618
% 0.20/0.49  % (31876)Time elapsed: 0.081 s
% 0.20/0.49  % (31876)------------------------------
% 0.20/0.49  % (31876)------------------------------
% 0.20/0.49  % (31862)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (31870)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (31861)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (31859)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (31857)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (31858)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.51  % (31867)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (31866)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (31864)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (31874)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (31868)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (31871)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (31873)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  % (31872)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.55  % (31875)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f3355,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f111,f120,f167,f196,f202,f277,f814,f1422,f1657,f1672,f1855,f1867,f1920,f1921,f3325,f3328,f3354])).
% 0.20/0.55  fof(f3354,plain,(
% 0.20/0.55    spl4_2 | ~spl4_6 | ~spl4_10 | ~spl4_12 | ~spl4_14),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f3353])).
% 0.20/0.55  fof(f3353,plain,(
% 0.20/0.55    $false | (spl4_2 | ~spl4_6 | ~spl4_10 | ~spl4_12 | ~spl4_14)),
% 0.20/0.55    inference(subsumption_resolution,[],[f3186,f3351])).
% 0.20/0.55  fof(f3351,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.55    inference(forward_demodulation,[],[f106,f163])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f154,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f22])).
% 0.20/0.55  fof(f22,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f21])).
% 0.20/0.55  fof(f21,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    ( ! [X2] : (k2_partfun1(sK0,sK1,sK3,X2) = k7_relat_1(sK3,X2) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(resolution,[],[f55,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f3186,plain,(
% 0.20/0.55    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_6 | ~spl4_10 | ~spl4_12 | ~spl4_14)),
% 0.20/0.55    inference(resolution,[],[f3161,f269])).
% 0.20/0.55  fof(f269,plain,(
% 0.20/0.55    ( ! [X4] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),sK1)) ) | (~spl4_6 | ~spl4_12)),
% 0.20/0.55    inference(subsumption_resolution,[],[f265,f184])).
% 0.20/0.55  fof(f184,plain,(
% 0.20/0.55    ( ! [X7] : (v1_relat_1(k7_relat_1(sK3,X7))) ) | ~spl4_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f183])).
% 0.20/0.55  fof(f183,plain,(
% 0.20/0.55    spl4_12 <=> ! [X7] : v1_relat_1(k7_relat_1(sK3,X7))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.55  fof(f265,plain,(
% 0.20/0.55    ( ! [X4] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X4))) ) | ~spl4_6),
% 0.20/0.55    inference(resolution,[],[f190,f86])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.55  fof(f190,plain,(
% 0.20/0.55    ( ! [X1] : (v5_relat_1(k7_relat_1(sK3,X1),sK1)) ) | ~spl4_6),
% 0.20/0.55    inference(subsumption_resolution,[],[f187,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    v1_relat_1(sK3) | ~spl4_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f127])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    spl4_6 <=> v1_relat_1(sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    ( ! [X1] : (v5_relat_1(k7_relat_1(sK3,X1),sK1) | ~v1_relat_1(sK3)) )),
% 0.20/0.55    inference(resolution,[],[f159,f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v5_relat_1(k7_relat_1(X2,X0),X1) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))) | (~v5_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v1_relat_1(X2)) => (v5_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    v5_relat_1(sK3,sK1)),
% 0.20/0.55    inference(resolution,[],[f55,f91])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.55  fof(f3161,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0)) ) | (~spl4_6 | ~spl4_10 | ~spl4_14)),
% 0.20/0.55    inference(forward_demodulation,[],[f3160,f163])).
% 0.20/0.55  fof(f3160,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0)) ) | (~spl4_6 | ~spl4_10 | ~spl4_14)),
% 0.20/0.55    inference(forward_demodulation,[],[f3159,f2774])).
% 0.20/0.55  fof(f2774,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_6 | ~spl4_10)),
% 0.20/0.55    inference(resolution,[],[f1958,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    r1_tarski(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f1958,plain,(
% 0.20/0.55    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2) ) | (~spl4_6 | ~spl4_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1952,f128])).
% 0.20/0.55  fof(f1952,plain,(
% 0.20/0.55    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_relat_1(k7_relat_1(sK3,X2)) = X2 | ~v1_relat_1(sK3)) ) | ~spl4_10),
% 0.20/0.55    inference(superposition,[],[f74,f1946])).
% 0.20/0.55  fof(f1946,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK3) | ~spl4_10),
% 0.20/0.55    inference(subsumption_resolution,[],[f1942,f55])).
% 0.20/0.55  fof(f1942,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 0.20/0.55    inference(superposition,[],[f150,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f148])).
% 0.20/0.55  fof(f148,plain,(
% 0.20/0.55    spl4_10 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.55  fof(f3159,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0)) ) | ~spl4_14),
% 0.20/0.55    inference(forward_demodulation,[],[f227,f163])).
% 0.20/0.55  fof(f227,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0)) ) | ~spl4_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f226])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    spl4_14 <=> ! [X0] : (v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.55  fof(f3328,plain,(
% 0.20/0.55    ~spl4_12 | spl4_13),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f3327])).
% 0.20/0.55  fof(f3327,plain,(
% 0.20/0.55    $false | (~spl4_12 | spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f3326,f184])).
% 0.20/0.55  fof(f3326,plain,(
% 0.20/0.55    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_13),
% 0.20/0.55    inference(forward_demodulation,[],[f224,f163])).
% 0.20/0.55  fof(f224,plain,(
% 0.20/0.55    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f222])).
% 0.20/0.55  fof(f222,plain,(
% 0.20/0.55    spl4_13 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.55  fof(f3325,plain,(
% 0.20/0.55    spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_12 | ~spl4_15),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f3324])).
% 0.20/0.55  fof(f3324,plain,(
% 0.20/0.55    $false | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_12 | ~spl4_15)),
% 0.20/0.55    inference(subsumption_resolution,[],[f3321,f274])).
% 0.20/0.55  fof(f274,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.55    inference(subsumption_resolution,[],[f273,f53])).
% 0.20/0.55  fof(f273,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 0.20/0.55    inference(subsumption_resolution,[],[f272,f55])).
% 0.20/0.55  fof(f272,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_3),
% 0.20/0.55    inference(superposition,[],[f110,f61])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.55  fof(f3321,plain,(
% 0.20/0.55    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_6 | ~spl4_10 | ~spl4_12 | ~spl4_15)),
% 0.20/0.55    inference(resolution,[],[f3296,f269])).
% 0.20/0.55  fof(f3296,plain,(
% 0.20/0.55    ( ! [X1] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | (~spl4_6 | ~spl4_10 | ~spl4_15)),
% 0.20/0.55    inference(forward_demodulation,[],[f3295,f163])).
% 0.20/0.55  fof(f3295,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_15)),
% 0.20/0.55    inference(forward_demodulation,[],[f3294,f2774])).
% 0.20/0.55  fof(f3294,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1)) ) | ~spl4_15),
% 0.20/0.55    inference(forward_demodulation,[],[f231,f163])).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1)) ) | ~spl4_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f230])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    spl4_15 <=> ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.55  fof(f1921,plain,(
% 0.20/0.55    ~spl4_13 | spl4_15 | ~spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f1915,f100,f230,f222])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.55  fof(f1915,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1))) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X1) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_1),
% 0.20/0.55    inference(resolution,[],[f101,f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f100])).
% 0.20/0.55  fof(f1920,plain,(
% 0.20/0.55    ~spl4_13 | spl4_14 | ~spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f1914,f100,f226,f222])).
% 0.20/0.55  fof(f1914,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X0) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_1),
% 0.20/0.55    inference(resolution,[],[f101,f84])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f1867,plain,(
% 0.20/0.55    spl4_11 | spl4_12 | ~spl4_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f1863,f127,f183,f180])).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    spl4_11 <=> ! [X8] : ~v5_relat_1(sK3,X8)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.55  fof(f1863,plain,(
% 0.20/0.55    ( ! [X8,X7] : (v1_relat_1(k7_relat_1(sK3,X7)) | ~v5_relat_1(sK3,X8)) ) | ~spl4_6),
% 0.20/0.55    inference(resolution,[],[f128,f89])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f44])).
% 0.20/0.55  fof(f1855,plain,(
% 0.20/0.55    ~spl4_9 | spl4_10 | spl4_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f1854,f113,f148,f144])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    spl4_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    spl4_4 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.55  fof(f1854,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f1853,f115])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f113])).
% 0.20/0.55  fof(f1853,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(resolution,[],[f54,f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f1672,plain,(
% 0.20/0.55    spl4_3 | ~spl4_5 | ~spl4_21 | ~spl4_25),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f1671])).
% 0.20/0.55  fof(f1671,plain,(
% 0.20/0.55    $false | (spl4_3 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1670,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.55  fof(f1670,plain,(
% 0.20/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(forward_demodulation,[],[f1669,f836])).
% 0.20/0.55  fof(f836,plain,(
% 0.20/0.55    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl4_25),
% 0.20/0.55    inference(forward_demodulation,[],[f821,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.55  fof(f821,plain,(
% 0.20/0.55    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl4_25),
% 0.20/0.55    inference(resolution,[],[f695,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.55  fof(f695,plain,(
% 0.20/0.55    v1_relat_1(k1_xboole_0) | ~spl4_25),
% 0.20/0.55    inference(avatar_component_clause,[],[f694])).
% 0.20/0.55  fof(f694,plain,(
% 0.20/0.55    spl4_25 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.55  fof(f1669,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(forward_demodulation,[],[f1668,f470])).
% 0.20/0.55  fof(f470,plain,(
% 0.20/0.55    k1_xboole_0 = sK3 | ~spl4_21),
% 0.20/0.55    inference(avatar_component_clause,[],[f468])).
% 0.20/0.55  fof(f468,plain,(
% 0.20/0.55    spl4_21 <=> k1_xboole_0 = sK3),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.55  fof(f1668,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_3 | ~spl4_5 | ~spl4_25)),
% 0.20/0.55    inference(forward_demodulation,[],[f1667,f98])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(flattening,[],[f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f1667,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (spl4_3 | ~spl4_5 | ~spl4_25)),
% 0.20/0.55    inference(forward_demodulation,[],[f274,f1412])).
% 0.20/0.55  fof(f1412,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_25)),
% 0.20/0.55    inference(resolution,[],[f1189,f295])).
% 0.20/0.55  fof(f295,plain,(
% 0.20/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl4_5),
% 0.20/0.55    inference(backward_demodulation,[],[f56,f119])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f117])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    spl4_5 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f1189,plain,(
% 0.20/0.55    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) ) | ~spl4_25),
% 0.20/0.55    inference(forward_demodulation,[],[f1188,f76])).
% 0.20/0.55  fof(f1188,plain,(
% 0.20/0.55    ( ! [X4] : (k1_xboole_0 = X4 | ~r1_tarski(X4,k1_relat_1(k1_xboole_0))) ) | ~spl4_25),
% 0.20/0.55    inference(forward_demodulation,[],[f1187,f76])).
% 0.20/0.55  fof(f1187,plain,(
% 0.20/0.55    ( ! [X4] : (k1_relat_1(k1_xboole_0) = X4 | ~r1_tarski(X4,k1_relat_1(k1_xboole_0))) ) | ~spl4_25),
% 0.20/0.55    inference(subsumption_resolution,[],[f1182,f695])).
% 0.20/0.55  fof(f1182,plain,(
% 0.20/0.55    ( ! [X4] : (k1_relat_1(k1_xboole_0) = X4 | ~r1_tarski(X4,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_25),
% 0.20/0.55    inference(superposition,[],[f74,f1133])).
% 0.20/0.55  fof(f1133,plain,(
% 0.20/0.55    ( ! [X2] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)) ) | ~spl4_25),
% 0.20/0.55    inference(subsumption_resolution,[],[f1132,f695])).
% 0.20/0.55  fof(f1132,plain,(
% 0.20/0.55    ( ! [X2] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X2) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_25),
% 0.20/0.55    inference(subsumption_resolution,[],[f1128,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.55  fof(f1128,plain,(
% 0.20/0.55    ( ! [X2] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X2) | ~r1_tarski(k1_xboole_0,X2) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_25),
% 0.20/0.55    inference(superposition,[],[f69,f836])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.20/0.55  fof(f1657,plain,(
% 0.20/0.55    spl4_2 | ~spl4_5 | ~spl4_21 | ~spl4_25),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f1656])).
% 0.20/0.55  fof(f1656,plain,(
% 0.20/0.55    $false | (spl4_2 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1655,f1579])).
% 0.20/0.55  fof(f1579,plain,(
% 0.20/0.55    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl4_5 | ~spl4_21)),
% 0.20/0.55    inference(backward_demodulation,[],[f760,f470])).
% 0.20/0.55  fof(f760,plain,(
% 0.20/0.55    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_5),
% 0.20/0.55    inference(forward_demodulation,[],[f54,f119])).
% 0.20/0.55  fof(f1655,plain,(
% 0.20/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl4_2 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(forward_demodulation,[],[f1654,f836])).
% 0.20/0.55  fof(f1654,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1653,f662])).
% 0.20/0.55  fof(f662,plain,(
% 0.20/0.55    v1_funct_1(k1_xboole_0) | ~spl4_21),
% 0.20/0.55    inference(backward_demodulation,[],[f53,f470])).
% 0.20/0.55  fof(f1653,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k1_xboole_0) | (spl4_2 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1633,f78])).
% 0.20/0.55  fof(f1633,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_1(k1_xboole_0) | (spl4_2 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(superposition,[],[f1583,f61])).
% 0.20/0.55  fof(f1583,plain,(
% 0.20/0.55    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_5 | ~spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(backward_demodulation,[],[f1430,f470])).
% 0.20/0.55  fof(f1430,plain,(
% 0.20/0.55    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_2 | ~spl4_5 | ~spl4_25)),
% 0.20/0.55    inference(backward_demodulation,[],[f756,f1412])).
% 0.20/0.55  fof(f756,plain,(
% 0.20/0.55    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,sK2),sK2,sK1) | (spl4_2 | ~spl4_5)),
% 0.20/0.55    inference(forward_demodulation,[],[f106,f119])).
% 0.20/0.55  fof(f1422,plain,(
% 0.20/0.55    ~spl4_5 | spl4_21 | ~spl4_25),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f1421])).
% 0.20/0.55  fof(f1421,plain,(
% 0.20/0.55    $false | (~spl4_5 | spl4_21 | ~spl4_25)),
% 0.20/0.55    inference(subsumption_resolution,[],[f1413,f469])).
% 0.20/0.55  fof(f469,plain,(
% 0.20/0.55    k1_xboole_0 != sK3 | spl4_21),
% 0.20/0.55    inference(avatar_component_clause,[],[f468])).
% 0.20/0.55  fof(f1413,plain,(
% 0.20/0.55    k1_xboole_0 = sK3 | (~spl4_5 | ~spl4_25)),
% 0.20/0.55    inference(resolution,[],[f1189,f755])).
% 0.20/0.55  fof(f755,plain,(
% 0.20/0.55    r1_tarski(sK3,k1_xboole_0) | ~spl4_5),
% 0.20/0.55    inference(forward_demodulation,[],[f754,f98])).
% 0.20/0.55  fof(f754,plain,(
% 0.20/0.55    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl4_5),
% 0.20/0.55    inference(forward_demodulation,[],[f160,f119])).
% 0.20/0.55  fof(f160,plain,(
% 0.20/0.55    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f55,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.55  fof(f814,plain,(
% 0.20/0.55    spl4_25),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f813])).
% 0.20/0.55  fof(f813,plain,(
% 0.20/0.55    $false | spl4_25),
% 0.20/0.55    inference(subsumption_resolution,[],[f805,f78])).
% 0.20/0.55  fof(f805,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_25),
% 0.20/0.55    inference(resolution,[],[f696,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f696,plain,(
% 0.20/0.55    ~v1_relat_1(k1_xboole_0) | spl4_25),
% 0.20/0.55    inference(avatar_component_clause,[],[f694])).
% 0.20/0.55  fof(f277,plain,(
% 0.20/0.55    spl4_9),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f276])).
% 0.20/0.55  fof(f276,plain,(
% 0.20/0.55    $false | spl4_9),
% 0.20/0.55    inference(subsumption_resolution,[],[f146,f55])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f144])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    ~spl4_11),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f199])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    $false | ~spl4_11),
% 0.20/0.55    inference(resolution,[],[f181,f159])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    ( ! [X8] : (~v5_relat_1(sK3,X8)) ) | ~spl4_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f180])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    spl4_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f195])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    $false | spl4_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f194,f53])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    ~v1_funct_1(sK3) | spl4_1),
% 0.20/0.55    inference(subsumption_resolution,[],[f192,f55])).
% 0.20/0.55  fof(f192,plain,(
% 0.20/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_1),
% 0.20/0.55    inference(resolution,[],[f102,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f100])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    spl4_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    $false | spl4_6),
% 0.20/0.55    inference(subsumption_resolution,[],[f158,f129])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    ~v1_relat_1(sK3) | spl4_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f127])).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    v1_relat_1(sK3)),
% 0.20/0.55    inference(resolution,[],[f55,f88])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    ~spl4_4 | spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f57,f117,f113])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f58,f108,f104,f100])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (31875)------------------------------
% 0.20/0.55  % (31875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31875)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (31875)Memory used [KB]: 7164
% 0.20/0.55  % (31875)Time elapsed: 0.152 s
% 0.20/0.55  % (31875)------------------------------
% 0.20/0.55  % (31875)------------------------------
% 0.20/0.55  % (31855)Success in time 0.2 s
%------------------------------------------------------------------------------
