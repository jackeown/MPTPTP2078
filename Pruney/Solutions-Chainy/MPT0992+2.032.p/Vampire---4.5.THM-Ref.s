%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:14 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  138 (5113 expanded)
%              Number of leaves         :   18 (1212 expanded)
%              Depth                    :   27
%              Number of atoms          :  407 (28979 expanded)
%              Number of equality atoms :  129 (6553 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1088,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1087,f1041])).

fof(f1041,plain,(
    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f973,f972])).

fof(f972,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f61,f971])).

fof(f971,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f642,f872,f969])).

fof(f969,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f968])).

fof(f968,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f887,f413])).

fof(f413,plain,
    ( sK3 = k1_relat_1(k7_relat_1(sK4,sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f290,f60])).

fof(f60,plain,(
    r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f47])).

fof(f47,plain,
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
   => ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
        | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f290,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | k1_relat_1(k7_relat_1(sK4,X2)) = X2
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f288,f106])).

fof(f106,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f77,f59])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f288,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | k1_relat_1(k7_relat_1(sK4,X2)) = X2
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f66,f278])).

fof(f278,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f270,f145])).

fof(f145,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f78,f59])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f270,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f269,f133])).

fof(f133,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f85,f59])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f269,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f81,f58])).

fof(f58,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) = X0
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f887,plain,(
    ! [X0] :
      ( v1_funct_2(k7_relat_1(sK4,X0),k1_relat_1(k7_relat_1(sK4,X0)),sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f883,f865])).

fof(f865,plain,(
    ! [X2] : k1_relat_1(k7_relat_1(sK4,X2)) = k1_relset_1(k1_relat_1(k7_relat_1(sK4,X2)),sK2,k7_relat_1(sK4,X2)) ),
    inference(resolution,[],[f859,f78])).

fof(f859,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),sK2))) ),
    inference(resolution,[],[f230,f179])).

fof(f179,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) ),
    inference(subsumption_resolution,[],[f177,f170])).

fof(f170,plain,(
    ! [X6] : v1_relat_1(k7_relat_1(sK4,X6)) ),
    inference(resolution,[],[f163,f77])).

fof(f163,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f159,f109])).

fof(f109,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK4,X0),sK4) ),
    inference(resolution,[],[f106,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f159,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    inference(resolution,[],[f89,f59])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f177,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2)
      | ~ v1_relat_1(k7_relat_1(sK4,X0)) ) ),
    inference(resolution,[],[f168,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f168,plain,(
    ! [X4] : v5_relat_1(k7_relat_1(sK4,X4),sK2) ),
    inference(resolution,[],[f163,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f230,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,X3)),X4)
      | m1_subset_1(k7_relat_1(sK4,X3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X3)),X4))) ) ),
    inference(resolution,[],[f184,f170])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(resolution,[],[f76,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f883,plain,(
    ! [X0] :
      ( k1_relat_1(k7_relat_1(sK4,X0)) != k1_relset_1(k1_relat_1(k7_relat_1(sK4,X0)),sK2,k7_relat_1(sK4,X0))
      | k1_xboole_0 = sK2
      | v1_funct_2(k7_relat_1(sK4,X0),k1_relat_1(k7_relat_1(sK4,X0)),sK2) ) ),
    inference(resolution,[],[f866,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 = X2
      | v1_funct_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f866,plain,(
    ! [X3] : sP0(k1_relat_1(k7_relat_1(sK4,X3)),k7_relat_1(sK4,X3),sK2) ),
    inference(resolution,[],[f859,f85])).

fof(f872,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f859,f413])).

fof(f642,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)
    | ~ m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(subsumption_resolution,[],[f638,f641])).

fof(f641,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(subsumption_resolution,[],[f640,f57])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f640,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK4,X0))
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f639,f59])).

fof(f639,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK4,X0))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(sK4) ) ),
    inference(superposition,[],[f91,f630])).

fof(f630,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0) ),
    inference(resolution,[],[f471,f59])).

fof(f471,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2) ) ),
    inference(resolution,[],[f90,f57])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f638,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)
    | ~ m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k7_relat_1(sK4,sK3)) ),
    inference(forward_demodulation,[],[f637,f630])).

fof(f637,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k7_relat_1(sK4,sK3))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) ),
    inference(forward_demodulation,[],[f636,f630])).

fof(f636,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK3))
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) ),
    inference(backward_demodulation,[],[f62,f630])).

fof(f62,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f61,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f973,plain,(
    v1_funct_2(sK4,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f58,f971])).

fof(f1087,plain,(
    ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1084,f1033])).

fof(f1033,plain,(
    sK4 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f130,f972])).

fof(f130,plain,(
    sK4 = k7_relat_1(sK4,sK1) ),
    inference(subsumption_resolution,[],[f129,f106])).

fof(f129,plain,
    ( sK4 = k7_relat_1(sK4,sK1)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f69,f113])).

fof(f113,plain,(
    v4_relat_1(sK4,sK1) ),
    inference(resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f1084,plain,(
    ~ v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1078,f1081])).

fof(f1081,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f1029,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f1029,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f60,f972])).

fof(f1078,plain,(
    ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1077,f971])).

fof(f1077,plain,(
    ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) ),
    inference(subsumption_resolution,[],[f1076,f1047])).

fof(f1047,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK4,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1044,f1046])).

fof(f1046,plain,(
    ! [X0,X1] : k7_relat_1(sK4,X1) = k2_partfun1(X0,k1_xboole_0,sK4,X1) ),
    inference(subsumption_resolution,[],[f634,f1042])).

fof(f1042,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f974,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f974,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f59,f971])).

fof(f634,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
      | k7_relat_1(sK4,X1) = k2_partfun1(X0,k1_xboole_0,sK4,X1) ) ),
    inference(superposition,[],[f471,f95])).

fof(f1044,plain,(
    ! [X0,X1] : m1_subset_1(k2_partfun1(X0,k1_xboole_0,sK4,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f697,f1042])).

fof(f697,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(k2_partfun1(X0,k1_xboole_0,sK4,X1),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f584,f95])).

fof(f584,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,sK4,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f92,f57])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1076,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) ),
    inference(forward_demodulation,[],[f1024,f95])).

fof(f1024,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) ),
    inference(backward_demodulation,[],[f642,f971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (10150)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (10160)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (10151)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (10148)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (10149)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (10171)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (10162)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (10147)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (10154)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (10165)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.19/0.52  % (10159)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.19/0.52  % (10163)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.19/0.52  % (10156)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.19/0.53  % (10152)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.19/0.53  % (10170)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.19/0.53  % (10166)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.19/0.53  % (10173)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.19/0.53  % (10169)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.19/0.53  % (10161)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.19/0.54  % (10155)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.19/0.54  % (10157)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.35/0.54  % (10153)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.35/0.54  % (10167)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.35/0.54  % (10164)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.35/0.55  % (10158)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.35/0.55  % (10172)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.35/0.57  % (10150)Refutation found. Thanks to Tanya!
% 1.35/0.57  % SZS status Theorem for theBenchmark
% 1.35/0.60  % SZS output start Proof for theBenchmark
% 1.35/0.60  fof(f1088,plain,(
% 1.35/0.60    $false),
% 1.35/0.60    inference(subsumption_resolution,[],[f1087,f1041])).
% 1.35/0.60  fof(f1041,plain,(
% 1.35/0.60    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 1.35/0.60    inference(forward_demodulation,[],[f973,f972])).
% 1.35/0.60  fof(f972,plain,(
% 1.35/0.60    k1_xboole_0 = sK1),
% 1.35/0.60    inference(subsumption_resolution,[],[f61,f971])).
% 1.35/0.60  fof(f971,plain,(
% 1.35/0.60    k1_xboole_0 = sK2),
% 1.35/0.60    inference(global_subsumption,[],[f642,f872,f969])).
% 1.35/0.60  fof(f969,plain,(
% 1.35/0.60    v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) | k1_xboole_0 = sK2),
% 1.35/0.60    inference(duplicate_literal_removal,[],[f968])).
% 1.35/0.60  fof(f968,plain,(
% 1.35/0.60    v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.35/0.60    inference(superposition,[],[f887,f413])).
% 1.35/0.60  fof(f413,plain,(
% 1.35/0.60    sK3 = k1_relat_1(k7_relat_1(sK4,sK3)) | k1_xboole_0 = sK2),
% 1.35/0.60    inference(resolution,[],[f290,f60])).
% 1.35/0.60  fof(f60,plain,(
% 1.35/0.60    r1_tarski(sK3,sK1)),
% 1.35/0.60    inference(cnf_transformation,[],[f48])).
% 1.35/0.60  fof(f48,plain,(
% 1.35/0.60    (~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.35/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f47])).
% 1.35/0.60  fof(f47,plain,(
% 1.35/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.35/0.60    introduced(choice_axiom,[])).
% 1.35/0.60  fof(f21,plain,(
% 1.35/0.60    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.35/0.60    inference(flattening,[],[f20])).
% 1.35/0.60  fof(f20,plain,(
% 1.35/0.60    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.35/0.60    inference(ennf_transformation,[],[f19])).
% 1.35/0.60  fof(f19,negated_conjecture,(
% 1.35/0.60    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.35/0.60    inference(negated_conjecture,[],[f18])).
% 1.35/0.60  fof(f18,conjecture,(
% 1.35/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 1.35/0.60  fof(f290,plain,(
% 1.35/0.60    ( ! [X2] : (~r1_tarski(X2,sK1) | k1_relat_1(k7_relat_1(sK4,X2)) = X2 | k1_xboole_0 = sK2) )),
% 1.35/0.60    inference(subsumption_resolution,[],[f288,f106])).
% 1.35/0.60  fof(f106,plain,(
% 1.35/0.60    v1_relat_1(sK4)),
% 1.35/0.60    inference(resolution,[],[f77,f59])).
% 1.35/0.60  fof(f59,plain,(
% 1.35/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.35/0.60    inference(cnf_transformation,[],[f48])).
% 1.35/0.60  fof(f77,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f32])).
% 1.35/0.60  fof(f32,plain,(
% 1.35/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.60    inference(ennf_transformation,[],[f10])).
% 1.35/0.60  fof(f10,axiom,(
% 1.35/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.35/0.60  fof(f288,plain,(
% 1.35/0.60    ( ! [X2] : (~r1_tarski(X2,sK1) | k1_relat_1(k7_relat_1(sK4,X2)) = X2 | ~v1_relat_1(sK4) | k1_xboole_0 = sK2) )),
% 1.35/0.60    inference(superposition,[],[f66,f278])).
% 1.35/0.60  fof(f278,plain,(
% 1.35/0.60    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 1.35/0.60    inference(superposition,[],[f270,f145])).
% 1.35/0.60  fof(f145,plain,(
% 1.35/0.60    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 1.35/0.60    inference(resolution,[],[f78,f59])).
% 1.35/0.60  fof(f78,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f33])).
% 1.35/0.60  fof(f33,plain,(
% 1.35/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.60    inference(ennf_transformation,[],[f12])).
% 1.35/0.60  fof(f12,axiom,(
% 1.35/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.35/0.60  fof(f270,plain,(
% 1.35/0.60    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 1.35/0.60    inference(subsumption_resolution,[],[f269,f133])).
% 1.35/0.60  fof(f133,plain,(
% 1.35/0.60    sP0(sK1,sK4,sK2)),
% 1.35/0.60    inference(resolution,[],[f85,f59])).
% 1.35/0.60  fof(f85,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f56])).
% 1.35/0.60  fof(f56,plain,(
% 1.35/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.60    inference(nnf_transformation,[],[f46])).
% 1.35/0.60  fof(f46,plain,(
% 1.35/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.60    inference(definition_folding,[],[f36,f45])).
% 1.35/0.60  fof(f45,plain,(
% 1.35/0.60    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.35/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.35/0.60  fof(f36,plain,(
% 1.35/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.60    inference(flattening,[],[f35])).
% 1.35/0.60  fof(f35,plain,(
% 1.35/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.60    inference(ennf_transformation,[],[f15])).
% 1.35/0.60  fof(f15,axiom,(
% 1.35/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.35/0.60  fof(f269,plain,(
% 1.35/0.60    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~sP0(sK1,sK4,sK2)),
% 1.35/0.60    inference(resolution,[],[f81,f58])).
% 1.35/0.60  fof(f58,plain,(
% 1.35/0.60    v1_funct_2(sK4,sK1,sK2)),
% 1.35/0.60    inference(cnf_transformation,[],[f48])).
% 1.35/0.60  fof(f81,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) = X0 | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f55])).
% 1.35/0.60  fof(f55,plain,(
% 1.35/0.60    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.35/0.60    inference(rectify,[],[f54])).
% 1.35/0.60  fof(f54,plain,(
% 1.35/0.60    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.35/0.60    inference(nnf_transformation,[],[f45])).
% 1.35/0.60  fof(f66,plain,(
% 1.35/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f26])).
% 1.35/0.60  fof(f26,plain,(
% 1.35/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.35/0.60    inference(flattening,[],[f25])).
% 1.35/0.60  fof(f25,plain,(
% 1.35/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.35/0.60    inference(ennf_transformation,[],[f9])).
% 1.35/0.60  fof(f9,axiom,(
% 1.35/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.35/0.60  fof(f887,plain,(
% 1.35/0.60    ( ! [X0] : (v1_funct_2(k7_relat_1(sK4,X0),k1_relat_1(k7_relat_1(sK4,X0)),sK2) | k1_xboole_0 = sK2) )),
% 1.35/0.60    inference(subsumption_resolution,[],[f883,f865])).
% 1.35/0.60  fof(f865,plain,(
% 1.35/0.60    ( ! [X2] : (k1_relat_1(k7_relat_1(sK4,X2)) = k1_relset_1(k1_relat_1(k7_relat_1(sK4,X2)),sK2,k7_relat_1(sK4,X2))) )),
% 1.35/0.60    inference(resolution,[],[f859,f78])).
% 1.35/0.60  fof(f859,plain,(
% 1.35/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X0)),sK2)))) )),
% 1.35/0.60    inference(resolution,[],[f230,f179])).
% 1.35/0.60  fof(f179,plain,(
% 1.35/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2)) )),
% 1.35/0.60    inference(subsumption_resolution,[],[f177,f170])).
% 1.35/0.60  fof(f170,plain,(
% 1.35/0.60    ( ! [X6] : (v1_relat_1(k7_relat_1(sK4,X6))) )),
% 1.35/0.60    inference(resolution,[],[f163,f77])).
% 1.35/0.60  fof(f163,plain,(
% 1.35/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) )),
% 1.35/0.60    inference(resolution,[],[f159,f109])).
% 1.35/0.60  fof(f109,plain,(
% 1.35/0.60    ( ! [X0] : (r1_tarski(k7_relat_1(sK4,X0),sK4)) )),
% 1.35/0.60    inference(resolution,[],[f106,f65])).
% 1.35/0.60  fof(f65,plain,(
% 1.35/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f24])).
% 1.35/0.60  fof(f24,plain,(
% 1.35/0.60    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.35/0.60    inference(ennf_transformation,[],[f8])).
% 1.35/0.60  fof(f8,axiom,(
% 1.35/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.35/0.60  fof(f159,plain,(
% 1.35/0.60    ( ! [X0] : (~r1_tarski(X0,sK4) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) )),
% 1.35/0.60    inference(resolution,[],[f89,f59])).
% 1.35/0.60  fof(f89,plain,(
% 1.35/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.35/0.60    inference(cnf_transformation,[],[f40])).
% 1.35/0.60  fof(f40,plain,(
% 1.35/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.35/0.60    inference(flattening,[],[f39])).
% 1.35/0.60  fof(f39,plain,(
% 1.35/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 1.35/0.60    inference(ennf_transformation,[],[f14])).
% 1.35/0.60  fof(f14,axiom,(
% 1.35/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).
% 1.35/0.60  fof(f177,plain,(
% 1.35/0.60    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) | ~v1_relat_1(k7_relat_1(sK4,X0))) )),
% 1.35/0.60    inference(resolution,[],[f168,f67])).
% 1.35/0.60  fof(f67,plain,(
% 1.35/0.60    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f49])).
% 1.35/0.60  fof(f49,plain,(
% 1.35/0.60    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.35/0.60    inference(nnf_transformation,[],[f27])).
% 1.35/0.60  fof(f27,plain,(
% 1.35/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.35/0.60    inference(ennf_transformation,[],[f5])).
% 1.35/0.60  fof(f5,axiom,(
% 1.35/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.35/0.60  fof(f168,plain,(
% 1.35/0.60    ( ! [X4] : (v5_relat_1(k7_relat_1(sK4,X4),sK2)) )),
% 1.35/0.60    inference(resolution,[],[f163,f80])).
% 1.35/0.60  fof(f80,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f34])).
% 1.35/0.60  fof(f34,plain,(
% 1.35/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.35/0.60    inference(ennf_transformation,[],[f11])).
% 1.35/0.60  fof(f11,axiom,(
% 1.35/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.35/0.60  fof(f230,plain,(
% 1.35/0.60    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(k7_relat_1(sK4,X3)),X4) | m1_subset_1(k7_relat_1(sK4,X3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK4,X3)),X4)))) )),
% 1.35/0.60    inference(resolution,[],[f184,f170])).
% 1.35/0.60  fof(f184,plain,(
% 1.35/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.35/0.60    inference(resolution,[],[f76,f93])).
% 1.35/0.60  fof(f93,plain,(
% 1.35/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.35/0.60    inference(equality_resolution,[],[f71])).
% 1.35/0.60  fof(f71,plain,(
% 1.35/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.35/0.60    inference(cnf_transformation,[],[f51])).
% 1.35/0.60  fof(f51,plain,(
% 1.35/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.60    inference(flattening,[],[f50])).
% 1.35/0.60  fof(f50,plain,(
% 1.35/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.60    inference(nnf_transformation,[],[f1])).
% 1.35/0.60  fof(f1,axiom,(
% 1.35/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.35/0.60  fof(f76,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_relat_1(X2)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f31])).
% 1.35/0.60  fof(f31,plain,(
% 1.35/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.35/0.60    inference(flattening,[],[f30])).
% 1.35/0.60  fof(f30,plain,(
% 1.35/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.35/0.60    inference(ennf_transformation,[],[f13])).
% 1.35/0.60  fof(f13,axiom,(
% 1.35/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.35/0.60  fof(f883,plain,(
% 1.35/0.60    ( ! [X0] : (k1_relat_1(k7_relat_1(sK4,X0)) != k1_relset_1(k1_relat_1(k7_relat_1(sK4,X0)),sK2,k7_relat_1(sK4,X0)) | k1_xboole_0 = sK2 | v1_funct_2(k7_relat_1(sK4,X0),k1_relat_1(k7_relat_1(sK4,X0)),sK2)) )),
% 1.35/0.60    inference(resolution,[],[f866,f83])).
% 1.35/0.60  fof(f83,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 = X2 | v1_funct_2(X1,X0,X2)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f55])).
% 1.35/0.60  fof(f866,plain,(
% 1.35/0.60    ( ! [X3] : (sP0(k1_relat_1(k7_relat_1(sK4,X3)),k7_relat_1(sK4,X3),sK2)) )),
% 1.35/0.60    inference(resolution,[],[f859,f85])).
% 1.35/0.60  fof(f872,plain,(
% 1.35/0.60    m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | k1_xboole_0 = sK2),
% 1.35/0.60    inference(superposition,[],[f859,f413])).
% 1.35/0.60  fof(f642,plain,(
% 1.35/0.60    ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) | ~m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 1.35/0.60    inference(subsumption_resolution,[],[f638,f641])).
% 1.35/0.60  fof(f641,plain,(
% 1.35/0.60    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 1.35/0.60    inference(subsumption_resolution,[],[f640,f57])).
% 1.35/0.60  fof(f57,plain,(
% 1.35/0.60    v1_funct_1(sK4)),
% 1.35/0.60    inference(cnf_transformation,[],[f48])).
% 1.35/0.60  fof(f640,plain,(
% 1.35/0.60    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0)) | ~v1_funct_1(sK4)) )),
% 1.35/0.60    inference(subsumption_resolution,[],[f639,f59])).
% 1.35/0.60  fof(f639,plain,(
% 1.35/0.60    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4)) )),
% 1.35/0.60    inference(superposition,[],[f91,f630])).
% 1.35/0.60  fof(f630,plain,(
% 1.35/0.60    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0)) )),
% 1.35/0.60    inference(resolution,[],[f471,f59])).
% 1.35/0.60  fof(f471,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2)) )),
% 1.35/0.60    inference(resolution,[],[f90,f57])).
% 1.35/0.60  fof(f90,plain,(
% 1.35/0.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f42])).
% 1.35/0.60  fof(f42,plain,(
% 1.35/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.35/0.60    inference(flattening,[],[f41])).
% 1.35/0.60  fof(f41,plain,(
% 1.35/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.35/0.60    inference(ennf_transformation,[],[f17])).
% 1.35/0.60  fof(f17,axiom,(
% 1.35/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.35/0.60  fof(f91,plain,(
% 1.35/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f44])).
% 1.35/0.60  fof(f44,plain,(
% 1.35/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.35/0.60    inference(flattening,[],[f43])).
% 1.35/0.60  fof(f43,plain,(
% 1.35/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.35/0.60    inference(ennf_transformation,[],[f16])).
% 1.35/0.60  fof(f16,axiom,(
% 1.35/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.35/0.60  fof(f638,plain,(
% 1.35/0.60    ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) | ~m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_1(k7_relat_1(sK4,sK3))),
% 1.35/0.60    inference(forward_demodulation,[],[f637,f630])).
% 1.35/0.60  fof(f637,plain,(
% 1.35/0.60    ~m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_1(k7_relat_1(sK4,sK3)) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)),
% 1.35/0.60    inference(forward_demodulation,[],[f636,f630])).
% 1.35/0.60  fof(f636,plain,(
% 1.35/0.60    ~v1_funct_1(k7_relat_1(sK4,sK3)) | ~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)),
% 1.35/0.60    inference(backward_demodulation,[],[f62,f630])).
% 1.35/0.60  fof(f62,plain,(
% 1.35/0.60    ~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))),
% 1.35/0.60    inference(cnf_transformation,[],[f48])).
% 1.35/0.60  fof(f61,plain,(
% 1.35/0.60    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.35/0.60    inference(cnf_transformation,[],[f48])).
% 1.35/0.60  fof(f973,plain,(
% 1.35/0.60    v1_funct_2(sK4,sK1,k1_xboole_0)),
% 1.35/0.60    inference(backward_demodulation,[],[f58,f971])).
% 1.35/0.60  fof(f1087,plain,(
% 1.35/0.60    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 1.35/0.60    inference(forward_demodulation,[],[f1084,f1033])).
% 1.35/0.60  fof(f1033,plain,(
% 1.35/0.60    sK4 = k7_relat_1(sK4,k1_xboole_0)),
% 1.35/0.60    inference(backward_demodulation,[],[f130,f972])).
% 1.35/0.60  fof(f130,plain,(
% 1.35/0.60    sK4 = k7_relat_1(sK4,sK1)),
% 1.35/0.60    inference(subsumption_resolution,[],[f129,f106])).
% 1.35/0.60  fof(f129,plain,(
% 1.35/0.60    sK4 = k7_relat_1(sK4,sK1) | ~v1_relat_1(sK4)),
% 1.35/0.60    inference(resolution,[],[f69,f113])).
% 1.35/0.60  fof(f113,plain,(
% 1.35/0.60    v4_relat_1(sK4,sK1)),
% 1.35/0.60    inference(resolution,[],[f79,f59])).
% 1.35/0.60  fof(f79,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f34])).
% 1.35/0.60  fof(f69,plain,(
% 1.35/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.35/0.60    inference(cnf_transformation,[],[f29])).
% 1.35/0.60  fof(f29,plain,(
% 1.35/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.35/0.60    inference(flattening,[],[f28])).
% 1.35/0.60  fof(f28,plain,(
% 1.35/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.35/0.60    inference(ennf_transformation,[],[f7])).
% 1.35/0.60  fof(f7,axiom,(
% 1.35/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.35/0.60  fof(f1084,plain,(
% 1.35/0.60    ~v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.35/0.60    inference(backward_demodulation,[],[f1078,f1081])).
% 1.35/0.60  fof(f1081,plain,(
% 1.35/0.60    k1_xboole_0 = sK3),
% 1.35/0.60    inference(resolution,[],[f1029,f63])).
% 1.35/0.60  fof(f63,plain,(
% 1.35/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.35/0.60    inference(cnf_transformation,[],[f22])).
% 1.35/0.60  fof(f22,plain,(
% 1.35/0.60    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.35/0.60    inference(ennf_transformation,[],[f3])).
% 1.35/0.60  fof(f3,axiom,(
% 1.35/0.60    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.35/0.60  fof(f1029,plain,(
% 1.35/0.60    r1_tarski(sK3,k1_xboole_0)),
% 1.35/0.60    inference(backward_demodulation,[],[f60,f972])).
% 1.35/0.60  fof(f1078,plain,(
% 1.35/0.60    ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0)),
% 1.35/0.60    inference(forward_demodulation,[],[f1077,f971])).
% 1.35/0.60  fof(f1077,plain,(
% 1.35/0.60    ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)),
% 1.35/0.60    inference(subsumption_resolution,[],[f1076,f1047])).
% 1.35/0.60  fof(f1047,plain,(
% 1.35/0.60    ( ! [X1] : (m1_subset_1(k7_relat_1(sK4,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.35/0.60    inference(forward_demodulation,[],[f1044,f1046])).
% 1.35/0.60  fof(f1046,plain,(
% 1.35/0.60    ( ! [X0,X1] : (k7_relat_1(sK4,X1) = k2_partfun1(X0,k1_xboole_0,sK4,X1)) )),
% 1.35/0.60    inference(subsumption_resolution,[],[f634,f1042])).
% 1.35/0.60  fof(f1042,plain,(
% 1.35/0.60    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 1.35/0.60    inference(forward_demodulation,[],[f974,f95])).
% 1.35/0.60  fof(f95,plain,(
% 1.35/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.35/0.60    inference(equality_resolution,[],[f75])).
% 1.35/0.60  fof(f75,plain,(
% 1.35/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.35/0.60    inference(cnf_transformation,[],[f53])).
% 1.35/0.60  fof(f53,plain,(
% 1.35/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.35/0.60    inference(flattening,[],[f52])).
% 1.35/0.60  fof(f52,plain,(
% 1.35/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.35/0.60    inference(nnf_transformation,[],[f4])).
% 1.35/0.60  fof(f4,axiom,(
% 1.35/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.35/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.35/0.60  fof(f974,plain,(
% 1.35/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.35/0.60    inference(backward_demodulation,[],[f59,f971])).
% 1.35/0.60  fof(f634,plain,(
% 1.35/0.60    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | k7_relat_1(sK4,X1) = k2_partfun1(X0,k1_xboole_0,sK4,X1)) )),
% 1.35/0.60    inference(superposition,[],[f471,f95])).
% 1.35/0.60  fof(f1044,plain,(
% 1.35/0.60    ( ! [X0,X1] : (m1_subset_1(k2_partfun1(X0,k1_xboole_0,sK4,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.35/0.60    inference(subsumption_resolution,[],[f697,f1042])).
% 1.35/0.60  fof(f697,plain,(
% 1.35/0.60    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_partfun1(X0,k1_xboole_0,sK4,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.35/0.60    inference(superposition,[],[f584,f95])).
% 1.35/0.60  fof(f584,plain,(
% 1.35/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK4,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/0.60    inference(resolution,[],[f92,f57])).
% 1.35/0.60  fof(f92,plain,(
% 1.35/0.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.35/0.61    inference(cnf_transformation,[],[f44])).
% 1.35/0.61  fof(f1076,plain,(
% 1.35/0.61    ~m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)),
% 1.35/0.61    inference(forward_demodulation,[],[f1024,f95])).
% 1.35/0.61  fof(f1024,plain,(
% 1.35/0.61    ~m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) | ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)),
% 1.35/0.61    inference(backward_demodulation,[],[f642,f971])).
% 1.35/0.61  % SZS output end Proof for theBenchmark
% 1.35/0.61  % (10150)------------------------------
% 1.35/0.61  % (10150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.61  % (10150)Termination reason: Refutation
% 1.35/0.61  
% 1.35/0.61  % (10150)Memory used [KB]: 7036
% 1.35/0.61  % (10150)Time elapsed: 0.151 s
% 1.35/0.61  % (10150)------------------------------
% 1.35/0.61  % (10150)------------------------------
% 1.35/0.61  % (10146)Success in time 0.238 s
%------------------------------------------------------------------------------
