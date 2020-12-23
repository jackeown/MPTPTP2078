%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 473 expanded)
%              Number of leaves         :   12 ( 109 expanded)
%              Depth                    :   21
%              Number of atoms          :  251 (1980 expanded)
%              Number of equality atoms :   92 ( 282 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(subsumption_resolution,[],[f181,f153])).

fof(f153,plain,(
    r2_relset_1(sK1,k1_xboole_0,sK4,sK4) ),
    inference(backward_demodulation,[],[f95,f149])).

fof(f149,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f148,f95])).

fof(f148,plain,
    ( ~ r2_relset_1(sK1,sK2,sK4,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f129,f147])).

fof(f147,plain,
    ( sK4 = k7_relat_1(sK4,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f144,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK4,X0)
      | sK4 = k7_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f46,f80])).

fof(f80,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
    & r1_tarski(sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
      & r1_tarski(sK1,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f144,plain,
    ( v4_relat_1(sK4,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f133,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f133,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f131,f43])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f123,f44])).

fof(f44,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK1,X0)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f63,f115])).

fof(f115,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f114,f98])).

fof(f98,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f113,f90])).

fof(f90,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f113,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f129,plain,(
    ~ r2_relset_1(sK1,sK2,k7_relat_1(sK4,sK3),sK4) ),
    inference(backward_demodulation,[],[f45,f125])).

fof(f125,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0) ),
    inference(resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ) ),
    inference(resolution,[],[f64,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f45,plain,(
    ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    r2_relset_1(sK1,sK2,sK4,sK4) ),
    inference(resolution,[],[f77,f43])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f181,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,sK4,sK4) ),
    inference(backward_demodulation,[],[f161,f177])).

fof(f177,plain,(
    ! [X0] : sK4 = k7_relat_1(sK4,X0) ),
    inference(subsumption_resolution,[],[f88,f169])).

fof(f169,plain,(
    ! [X1] : v4_relat_1(sK4,X1) ),
    inference(resolution,[],[f162,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f55,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f162,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f151,f69])).

fof(f151,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f43,f149])).

fof(f161,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK3),sK4) ),
    inference(backward_demodulation,[],[f129,f149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (9288)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (9279)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (9280)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (9277)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.49  % (9275)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (9280)Refutation not found, incomplete strategy% (9280)------------------------------
% 0.22/0.50  % (9280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9277)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f181,f153])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    r2_relset_1(sK1,k1_xboole_0,sK4,sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f95,f149])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    k1_xboole_0 = sK2),
% 0.22/0.50    inference(subsumption_resolution,[],[f148,f95])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,sK2,sK4,sK4) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(superposition,[],[f129,f147])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    sK4 = k7_relat_1(sK4,sK3) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(resolution,[],[f144,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0] : (~v4_relat_1(sK4,X0) | sK4 = k7_relat_1(sK4,X0)) )),
% 0.22/0.50    inference(resolution,[],[f46,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    v1_relat_1(sK4)),
% 0.22/0.50    inference(resolution,[],[f53,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    v4_relat_1(sK4,sK3) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(resolution,[],[f133,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(resolution,[],[f131,f43])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | k1_xboole_0 = sK2) )),
% 0.22/0.50    inference(resolution,[],[f123,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    r1_tarski(sK1,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(sK1,X0) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_xboole_0 = sK2) )),
% 0.22/0.50    inference(superposition,[],[f63,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(superposition,[],[f114,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 0.22/0.50    inference(resolution,[],[f54,f43])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 0.22/0.50    inference(subsumption_resolution,[],[f113,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    sP0(sK1,sK4,sK2)),
% 0.22/0.50    inference(resolution,[],[f60,f43])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(definition_folding,[],[f22,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~sP0(sK1,sK4,sK2)),
% 0.22/0.50    inference(resolution,[],[f56,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v1_funct_2(sK4,sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.50    inference(rectify,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f29])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,sK2,k7_relat_1(sK4,sK3),sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f45,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0)) )),
% 0.22/0.50    inference(resolution,[],[f124,f43])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)) )),
% 0.22/0.50    inference(resolution,[],[f64,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v1_funct_1(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    r2_relset_1(sK1,sK2,sK4,sK4)),
% 0.22/0.50    inference(resolution,[],[f77,f43])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(equality_resolution,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,k1_xboole_0,sK4,sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f161,f177])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ( ! [X0] : (sK4 = k7_relat_1(sK4,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f169])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X1] : (v4_relat_1(sK4,X1)) )),
% 0.22/0.50    inference(resolution,[],[f162,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 0.22/0.50    inference(superposition,[],[f55,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(flattening,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.50    inference(forward_demodulation,[],[f151,f69])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.22/0.50    inference(backward_demodulation,[],[f43,f149])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ~r2_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK3),sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f129,f149])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (9277)------------------------------
% 0.22/0.50  % (9277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9277)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (9277)Memory used [KB]: 6268
% 0.22/0.50  % (9277)Time elapsed: 0.081 s
% 0.22/0.50  % (9277)------------------------------
% 0.22/0.50  % (9277)------------------------------
% 0.22/0.50  % (9280)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  % (9273)Success in time 0.135 s
%------------------------------------------------------------------------------
