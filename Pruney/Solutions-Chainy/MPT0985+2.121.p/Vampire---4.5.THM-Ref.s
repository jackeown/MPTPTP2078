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
% DateTime   : Thu Dec  3 13:02:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  147 (5143 expanded)
%              Number of leaves         :   17 (1260 expanded)
%              Depth                    :   31
%              Number of atoms          :  452 (29879 expanded)
%              Number of equality atoms :  147 (5248 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(resolution,[],[f547,f156])).

fof(f156,plain,(
    ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ),
    inference(superposition,[],[f74,f136])).

fof(f136,plain,(
    ! [X1] : k1_xboole_0 = sK4(k1_xboole_0,X1) ),
    inference(resolution,[],[f129,f102])).

fof(f102,plain,(
    ! [X0] : r1_tarski(sK4(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,(
    ! [X1] : m1_subset_1(sK4(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f71,f88])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] : m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK4(X0,X1),X0,X1)
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1))
      & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK4(X0,X1),X0,X1)
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f129,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f65,f53])).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] : v1_funct_2(sK4(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f43])).

fof(f547,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(global_subsumption,[],[f141,f151,f546])).

fof(f546,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f545,f527])).

fof(f527,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f526])).

fof(f526,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f525,f335])).

fof(f335,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(global_subsumption,[],[f156,f334])).

fof(f334,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f329,f245])).

fof(f245,plain,(
    ! [X2,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(resolution,[],[f225,f53])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f329,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(resolution,[],[f90,f174])).

fof(f174,plain,(
    ! [X1] : sP0(k1_xboole_0,k1_xboole_0,X1) ),
    inference(superposition,[],[f170,f136])).

fof(f170,plain,(
    ! [X4,X3] : sP0(X3,sK4(X3,X4),X4) ),
    inference(resolution,[],[f82,f71])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f525,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f518,f480])).

fof(f480,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f272,f478])).

fof(f478,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f47,f105,f477])).

fof(f477,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f476,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f476,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f475])).

fof(f475,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f457,f418])).

fof(f418,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f327,f408])).

fof(f408,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f48,f407])).

fof(f407,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f403,f227])).

fof(f227,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f76,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f403,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f78,f169])).

fof(f169,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f82,f49])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f327,plain,(
    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) ),
    inference(global_subsumption,[],[f47,f105,f326])).

fof(f326,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f324,f218])).

fof(f218,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(global_subsumption,[],[f47,f105,f217])).

fof(f217,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f50])).

fof(f50,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f324,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f165,f264])).

fof(f264,plain,(
    sK2 = k1_relat_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f213,f258])).

fof(f258,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f253,f51])).

fof(f51,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f253,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f77,f49])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f213,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(global_subsumption,[],[f47,f105,f212])).

fof(f212,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f61,f50])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f165,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f59,f161])).

fof(f161,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f57,f60])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f457,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f446,f224])).

fof(f224,plain,
    ( ~ r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    inference(resolution,[],[f52,f67])).

fof(f52,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f446,plain,
    ( r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f429,f408])).

fof(f429,plain,(
    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3))) ),
    inference(resolution,[],[f394,f66])).

fof(f394,plain,(
    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) ),
    inference(global_subsumption,[],[f47,f105,f393])).

fof(f393,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f391,f218])).

fof(f391,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f200,f264])).

fof(f200,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f59,f196])).

fof(f196,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)))))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f58,f60])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f75,f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f272,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK3 ),
    inference(global_subsumption,[],[f105,f271])).

fof(f271,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f55,f258])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f518,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f438,f480])).

fof(f438,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f219,f428])).

fof(f428,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f394,f75])).

fof(f219,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | k1_xboole_0 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[],[f55,f218])).

fof(f545,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f544,f480])).

fof(f544,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f543,f527])).

fof(f543,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f542,f480])).

fof(f542,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f541,f478])).

fof(f541,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f540,f527])).

fof(f540,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f539,f480])).

fof(f539,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f484,f88])).

fof(f484,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f52,f478])).

fof(f151,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f73,f135])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = sK4(X0,k1_xboole_0) ),
    inference(resolution,[],[f129,f101])).

fof(f101,plain,(
    ! [X0] : r1_tarski(sK4(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f99,f66])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(sK4(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f71,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f141,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f99,f135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:22:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.44  % (30433)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.47  % (30433)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (30441)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.47  % (30421)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.48  % (30428)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.48  % (30429)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.48  % (30430)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f597,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(resolution,[],[f547,f156])).
% 0.19/0.48  fof(f156,plain,(
% 0.19/0.48    ( ! [X2] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.19/0.48    inference(superposition,[],[f74,f136])).
% 0.19/0.48  fof(f136,plain,(
% 0.19/0.48    ( ! [X1] : (k1_xboole_0 = sK4(k1_xboole_0,X1)) )),
% 0.19/0.48    inference(resolution,[],[f129,f102])).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(sK4(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.19/0.48    inference(resolution,[],[f100,f66])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.48    inference(nnf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.48  fof(f100,plain,(
% 0.19/0.48    ( ! [X1] : (m1_subset_1(sK4(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.19/0.48    inference(superposition,[],[f71,f88])).
% 0.19/0.48  fof(f88,plain,(
% 0.19/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f69])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f41])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.48    inference(flattening,[],[f40])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.48    inference(nnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.48  fof(f71,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f43])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ! [X0,X1] : (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK4(X0,X1),X0,X1) & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(pure_predicate_removal,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.19/0.48  fof(f12,axiom,(
% 0.19/0.48    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.19/0.48  fof(f129,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.48    inference(resolution,[],[f65,f53])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(flattening,[],[f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f74,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_funct_2(sK4(X0,X1),X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f43])).
% 0.19/0.48  fof(f547,plain,(
% 0.19/0.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.19/0.48    inference(global_subsumption,[],[f141,f151,f546])).
% 0.19/0.48  fof(f546,plain,(
% 0.19/0.48    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.48    inference(forward_demodulation,[],[f545,f527])).
% 0.19/0.48  fof(f527,plain,(
% 0.19/0.48    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f526])).
% 0.19/0.48  fof(f526,plain,(
% 0.19/0.48    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.19/0.48    inference(forward_demodulation,[],[f525,f335])).
% 0.19/0.48  fof(f335,plain,(
% 0.19/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.48    inference(global_subsumption,[],[f156,f334])).
% 0.19/0.48  fof(f334,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.19/0.48    inference(forward_demodulation,[],[f329,f245])).
% 0.19/0.48  fof(f245,plain,(
% 0.19/0.48    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 0.19/0.48    inference(resolution,[],[f225,f53])).
% 0.19/0.48  fof(f225,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.48    inference(resolution,[],[f76,f67])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f39])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.49  fof(f329,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.19/0.49    inference(resolution,[],[f90,f174])).
% 0.19/0.49  fof(f174,plain,(
% 0.19/0.49    ( ! [X1] : (sP0(k1_xboole_0,k1_xboole_0,X1)) )),
% 0.19/0.49    inference(superposition,[],[f170,f136])).
% 0.19/0.49  fof(f170,plain,(
% 0.19/0.49    ( ! [X4,X3] : (sP0(X3,sK4(X3,X4),X4)) )),
% 0.19/0.49    inference(resolution,[],[f82,f71])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f46])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(nnf_transformation,[],[f34])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(definition_folding,[],[f32,f33])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.19/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(flattening,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 0.19/0.49    inference(equality_resolution,[],[f79])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.19/0.49    inference(rectify,[],[f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.19/0.49    inference(nnf_transformation,[],[f33])).
% 0.19/0.49  fof(f525,plain,(
% 0.19/0.49    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.19/0.49    inference(forward_demodulation,[],[f518,f480])).
% 0.19/0.49  fof(f480,plain,(
% 0.19/0.49    k1_xboole_0 = sK3),
% 0.19/0.49    inference(subsumption_resolution,[],[f272,f478])).
% 0.19/0.49  fof(f478,plain,(
% 0.19/0.49    k1_xboole_0 = sK2),
% 0.19/0.49    inference(global_subsumption,[],[f47,f105,f477])).
% 0.19/0.49  fof(f477,plain,(
% 0.19/0.49    k1_xboole_0 = sK2 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(resolution,[],[f476,f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f24])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.49  fof(f476,plain,(
% 0.19/0.49    ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f475])).
% 0.19/0.49  fof(f475,plain,(
% 0.19/0.49    ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.19/0.49    inference(resolution,[],[f457,f418])).
% 0.19/0.49  fof(f418,plain,(
% 0.19/0.49    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | k1_xboole_0 = sK2),
% 0.19/0.49    inference(superposition,[],[f327,f408])).
% 0.19/0.49  fof(f408,plain,(
% 0.19/0.49    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.19/0.49    inference(global_subsumption,[],[f48,f407])).
% 0.19/0.49  fof(f407,plain,(
% 0.19/0.49    sK1 = k1_relat_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2),
% 0.19/0.49    inference(forward_demodulation,[],[f403,f227])).
% 0.19/0.49  fof(f227,plain,(
% 0.19/0.49    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.19/0.49    inference(resolution,[],[f76,f49])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f35])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.49    inference(flattening,[],[f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.49    inference(ennf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.19/0.49    inference(negated_conjecture,[],[f14])).
% 0.19/0.49  fof(f14,conjecture,(
% 0.19/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.19/0.49  fof(f403,plain,(
% 0.19/0.49    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.19/0.49    inference(resolution,[],[f78,f169])).
% 0.19/0.49  fof(f169,plain,(
% 0.19/0.49    sP0(sK1,sK3,sK2)),
% 0.19/0.49    inference(resolution,[],[f82,f49])).
% 0.19/0.49  fof(f78,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f45])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    v1_funct_2(sK3,sK1,sK2)),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f327,plain,(
% 0.19/0.49    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))),
% 0.19/0.49    inference(global_subsumption,[],[f47,f105,f326])).
% 0.19/0.49  fof(f326,plain,(
% 0.19/0.49    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(forward_demodulation,[],[f324,f218])).
% 0.19/0.49  fof(f218,plain,(
% 0.19/0.49    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(global_subsumption,[],[f47,f105,f217])).
% 0.19/0.49  fof(f217,plain,(
% 0.19/0.49    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(resolution,[],[f62,f50])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    v2_funct_1(sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.19/0.49  fof(f324,plain,(
% 0.19/0.49    v1_funct_2(k2_funct_1(sK3),sK2,k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(superposition,[],[f165,f264])).
% 0.19/0.49  fof(f264,plain,(
% 0.19/0.49    sK2 = k1_relat_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(backward_demodulation,[],[f213,f258])).
% 0.19/0.49  fof(f258,plain,(
% 0.19/0.49    sK2 = k2_relat_1(sK3)),
% 0.19/0.49    inference(forward_demodulation,[],[f253,f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f253,plain,(
% 0.19/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.19/0.49    inference(resolution,[],[f77,f49])).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f30])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.49  fof(f213,plain,(
% 0.19/0.49    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(global_subsumption,[],[f47,f105,f212])).
% 0.19/0.49  fof(f212,plain,(
% 0.19/0.49    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(resolution,[],[f61,f50])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f165,plain,(
% 0.19/0.49    ( ! [X0] : (v1_funct_2(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(global_subsumption,[],[f59,f161])).
% 0.19/0.49  fof(f161,plain,(
% 0.19/0.49    ( ! [X0] : (v1_funct_2(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(resolution,[],[f57,f60])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,axiom,(
% 0.19/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.19/0.49  fof(f59,plain,(
% 0.19/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f457,plain,(
% 0.19/0.49    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3)) | k1_xboole_0 = sK2),
% 0.19/0.49    inference(resolution,[],[f446,f224])).
% 0.19/0.49  fof(f224,plain,(
% 0.19/0.49    ~r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1)),
% 0.19/0.49    inference(resolution,[],[f52,f67])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f446,plain,(
% 0.19/0.49    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) | k1_xboole_0 = sK2),
% 0.19/0.49    inference(superposition,[],[f429,f408])).
% 0.19/0.49  fof(f429,plain,(
% 0.19/0.49    r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,k1_relat_1(sK3)))),
% 0.19/0.49    inference(resolution,[],[f394,f66])).
% 0.19/0.49  fof(f394,plain,(
% 0.19/0.49    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))),
% 0.19/0.49    inference(global_subsumption,[],[f47,f105,f393])).
% 0.19/0.49  fof(f393,plain,(
% 0.19/0.49    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(forward_demodulation,[],[f391,f218])).
% 0.19/0.49  fof(f391,plain,(
% 0.19/0.49    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK3))))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(superposition,[],[f200,f264])).
% 0.19/0.49  fof(f200,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(global_subsumption,[],[f59,f196])).
% 0.19/0.49  fof(f196,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0))))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(resolution,[],[f58,f60])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f23])).
% 0.19/0.49  fof(f105,plain,(
% 0.19/0.49    v1_relat_1(sK3)),
% 0.19/0.49    inference(resolution,[],[f75,f49])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    v1_funct_1(sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f36])).
% 0.19/0.49  fof(f272,plain,(
% 0.19/0.49    k1_xboole_0 != sK2 | k1_xboole_0 = sK3),
% 0.19/0.49    inference(global_subsumption,[],[f105,f271])).
% 0.19/0.49  fof(f271,plain,(
% 0.19/0.49    k1_xboole_0 != sK2 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3)),
% 0.19/0.49    inference(superposition,[],[f55,f258])).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(flattening,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.49  fof(f518,plain,(
% 0.19/0.49    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(sK3)),
% 0.19/0.49    inference(backward_demodulation,[],[f438,f480])).
% 0.19/0.49  fof(f438,plain,(
% 0.19/0.49    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = k2_funct_1(sK3)),
% 0.19/0.49    inference(subsumption_resolution,[],[f219,f428])).
% 0.19/0.49  fof(f428,plain,(
% 0.19/0.49    v1_relat_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(resolution,[],[f394,f75])).
% 0.19/0.49  fof(f219,plain,(
% 0.19/0.49    k1_xboole_0 != k1_relat_1(sK3) | k1_xboole_0 = k2_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(superposition,[],[f55,f218])).
% 0.19/0.49  fof(f545,plain,(
% 0.19/0.49    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.49    inference(forward_demodulation,[],[f544,f480])).
% 0.19/0.49  fof(f544,plain,(
% 0.19/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(forward_demodulation,[],[f543,f527])).
% 0.19/0.49  fof(f543,plain,(
% 0.19/0.49    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(forward_demodulation,[],[f542,f480])).
% 0.19/0.49  fof(f542,plain,(
% 0.19/0.49    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(forward_demodulation,[],[f541,f478])).
% 0.19/0.49  fof(f541,plain,(
% 0.19/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(forward_demodulation,[],[f540,f527])).
% 0.19/0.49  fof(f540,plain,(
% 0.19/0.49    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(forward_demodulation,[],[f539,f480])).
% 0.19/0.49  fof(f539,plain,(
% 0.19/0.49    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(forward_demodulation,[],[f484,f88])).
% 0.19/0.49  fof(f484,plain,(
% 0.19/0.49    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 0.19/0.49    inference(backward_demodulation,[],[f52,f478])).
% 0.19/0.49  fof(f151,plain,(
% 0.19/0.49    v1_funct_1(k1_xboole_0)),
% 0.19/0.49    inference(superposition,[],[f73,f135])).
% 0.19/0.49  fof(f135,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = sK4(X0,k1_xboole_0)) )),
% 0.19/0.49    inference(resolution,[],[f129,f101])).
% 0.19/0.49  fof(f101,plain,(
% 0.19/0.49    ( ! [X0] : (r1_tarski(sK4(X0,k1_xboole_0),k1_xboole_0)) )),
% 0.19/0.49    inference(resolution,[],[f99,f66])).
% 0.19/0.49  fof(f99,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(sK4(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.19/0.49    inference(superposition,[],[f71,f87])).
% 0.19/0.49  fof(f87,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.49    inference(equality_resolution,[],[f70])).
% 0.19/0.49  fof(f70,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f41])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f43])).
% 0.19/0.49  fof(f141,plain,(
% 0.19/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.19/0.49    inference(backward_demodulation,[],[f99,f135])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (30433)------------------------------
% 0.19/0.49  % (30433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (30433)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (30433)Memory used [KB]: 6652
% 0.19/0.49  % (30433)Time elapsed: 0.073 s
% 0.19/0.49  % (30433)------------------------------
% 0.19/0.49  % (30433)------------------------------
% 0.19/0.49  % (30420)Success in time 0.138 s
%------------------------------------------------------------------------------
