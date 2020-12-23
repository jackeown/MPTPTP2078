%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:24 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 419 expanded)
%              Number of leaves         :   12 (  97 expanded)
%              Depth                    :   20
%              Number of atoms          :  247 (1791 expanded)
%              Number of equality atoms :   96 ( 279 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f128,f108])).

fof(f108,plain,(
    r2_relset_1(sK1,k1_xboole_0,sK4,sK4) ),
    inference(backward_demodulation,[],[f85,f104])).

fof(f104,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f103,f85])).

fof(f103,plain,
    ( ~ r2_relset_1(sK1,sK2,sK4,sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f102,f97])).

fof(f97,plain,
    ( sK4 = k7_relat_1(sK4,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f96,f41])).

fof(f41,plain,(
    r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)
    & r1_tarski(sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f30])).

fof(f30,plain,
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

% (29232)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | sK4 = k7_relat_1(sK4,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(subsumption_resolution,[],[f95,f72])).

fof(f72,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | sK4 = k7_relat_1(sK4,X0)
      | ~ v1_relat_1(sK4)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f43,f93])).

fof(f93,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f92,f88])).

fof(f88,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f92,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f91,f39])).

fof(f39,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f51,f80])).

fof(f80,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f55,f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f102,plain,(
    ~ r2_relset_1(sK1,sK2,k7_relat_1(sK4,sK3),sK4) ),
    inference(backward_demodulation,[],[f42,f99])).

fof(f99,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0) ),
    inference(resolution,[],[f98,f40])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f42,plain,(
    ~ r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f85,plain,(
    r2_relset_1(sK1,sK2,sK4,sK4) ),
    inference(resolution,[],[f69,f40])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f128,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,sK4,sK4) ),
    inference(backward_demodulation,[],[f111,f124])).

fof(f124,plain,(
    ! [X0] : sK4 = k7_relat_1(sK4,X0) ),
    inference(subsumption_resolution,[],[f78,f117])).

fof(f117,plain,(
    ! [X1] : v4_relat_1(sK4,X1) ),
    inference(resolution,[],[f112,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f50,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f112,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f106,f61])).

fof(f106,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f40,f104])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK4,X0)
      | sK4 = k7_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f44,f72])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

% (29232)Refutation not found, incomplete strategy% (29232)------------------------------
% (29232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29232)Termination reason: Refutation not found, incomplete strategy

% (29232)Memory used [KB]: 6268
% (29232)Time elapsed: 0.138 s
% (29232)------------------------------
% (29232)------------------------------
% (29225)Refutation not found, incomplete strategy% (29225)------------------------------
% (29225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29225)Termination reason: Refutation not found, incomplete strategy

% (29225)Memory used [KB]: 10618
% (29225)Time elapsed: 0.137 s
% (29225)------------------------------
% (29225)------------------------------
fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f111,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK3),sK4) ),
    inference(backward_demodulation,[],[f102,f104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:09:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 1.21/0.55  % (29221)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.39/0.55  % (29231)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.39/0.55  % (29237)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.56  % (29229)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.39/0.56  % (29222)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.39/0.56  % (29239)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.39/0.56  % (29223)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.39/0.56  % (29226)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.39/0.56  % (29222)Refutation found. Thanks to Tanya!
% 1.39/0.56  % SZS status Theorem for theBenchmark
% 1.39/0.56  % (29225)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.39/0.57  % (29226)Refutation not found, incomplete strategy% (29226)------------------------------
% 1.39/0.57  % (29226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (29238)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.39/0.57  % (29224)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.39/0.57  % (29230)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.39/0.57  % (29224)Refutation not found, incomplete strategy% (29224)------------------------------
% 1.39/0.57  % (29224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (29224)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (29224)Memory used [KB]: 6140
% 1.39/0.57  % (29224)Time elapsed: 0.127 s
% 1.39/0.57  % (29224)------------------------------
% 1.39/0.57  % (29224)------------------------------
% 1.39/0.57  % (29234)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.39/0.57  % (29226)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (29226)Memory used [KB]: 1663
% 1.39/0.57  % (29226)Time elapsed: 0.117 s
% 1.39/0.57  % (29226)------------------------------
% 1.39/0.57  % (29226)------------------------------
% 1.39/0.57  % (29240)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.39/0.57  % (29242)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.39/0.57  % SZS output start Proof for theBenchmark
% 1.39/0.57  fof(f129,plain,(
% 1.39/0.57    $false),
% 1.39/0.57    inference(subsumption_resolution,[],[f128,f108])).
% 1.39/0.57  fof(f108,plain,(
% 1.39/0.57    r2_relset_1(sK1,k1_xboole_0,sK4,sK4)),
% 1.39/0.57    inference(backward_demodulation,[],[f85,f104])).
% 1.39/0.57  fof(f104,plain,(
% 1.39/0.57    k1_xboole_0 = sK2),
% 1.39/0.57    inference(subsumption_resolution,[],[f103,f85])).
% 1.39/0.57  fof(f103,plain,(
% 1.39/0.57    ~r2_relset_1(sK1,sK2,sK4,sK4) | k1_xboole_0 = sK2),
% 1.39/0.57    inference(superposition,[],[f102,f97])).
% 1.39/0.57  fof(f97,plain,(
% 1.39/0.57    sK4 = k7_relat_1(sK4,sK3) | k1_xboole_0 = sK2),
% 1.39/0.57    inference(resolution,[],[f96,f41])).
% 1.39/0.57  fof(f41,plain,(
% 1.39/0.57    r1_tarski(sK1,sK3)),
% 1.39/0.57    inference(cnf_transformation,[],[f31])).
% 1.39/0.57  fof(f31,plain,(
% 1.39/0.57    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.39/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f30])).
% 1.39/0.57  fof(f30,plain,(
% 1.39/0.57    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4) & r1_tarski(sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.39/0.57    introduced(choice_axiom,[])).
% 1.39/0.57  % (29232)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.39/0.57  fof(f14,plain,(
% 1.39/0.57    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.39/0.57    inference(flattening,[],[f13])).
% 1.39/0.57  fof(f13,plain,(
% 1.39/0.57    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.39/0.57    inference(ennf_transformation,[],[f11])).
% 1.39/0.57  fof(f11,negated_conjecture,(
% 1.39/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 1.39/0.57    inference(negated_conjecture,[],[f10])).
% 1.39/0.57  fof(f10,conjecture,(
% 1.39/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).
% 1.39/0.57  fof(f96,plain,(
% 1.39/0.57    ( ! [X0] : (~r1_tarski(sK1,X0) | sK4 = k7_relat_1(sK4,X0) | k1_xboole_0 = sK2) )),
% 1.39/0.57    inference(subsumption_resolution,[],[f95,f72])).
% 1.39/0.57  fof(f72,plain,(
% 1.39/0.57    v1_relat_1(sK4)),
% 1.39/0.57    inference(resolution,[],[f48,f40])).
% 1.39/0.57  fof(f40,plain,(
% 1.39/0.57    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.39/0.57    inference(cnf_transformation,[],[f31])).
% 1.39/0.57  fof(f48,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f19])).
% 1.39/0.57  fof(f19,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(ennf_transformation,[],[f4])).
% 1.39/0.57  fof(f4,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.39/0.57  fof(f95,plain,(
% 1.39/0.57    ( ! [X0] : (~r1_tarski(sK1,X0) | sK4 = k7_relat_1(sK4,X0) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2) )),
% 1.39/0.57    inference(superposition,[],[f43,f93])).
% 1.39/0.57  fof(f93,plain,(
% 1.39/0.57    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 1.39/0.57    inference(superposition,[],[f92,f88])).
% 1.39/0.57  fof(f88,plain,(
% 1.39/0.57    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)),
% 1.39/0.57    inference(resolution,[],[f49,f40])).
% 1.39/0.57  fof(f49,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f20])).
% 1.39/0.57  fof(f20,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(ennf_transformation,[],[f6])).
% 1.39/0.57  fof(f6,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.57  fof(f92,plain,(
% 1.39/0.57    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 1.39/0.57    inference(subsumption_resolution,[],[f91,f39])).
% 1.39/0.57  fof(f39,plain,(
% 1.39/0.57    v1_funct_2(sK4,sK1,sK2)),
% 1.39/0.57    inference(cnf_transformation,[],[f31])).
% 1.39/0.57  fof(f91,plain,(
% 1.39/0.57    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 1.39/0.57    inference(resolution,[],[f51,f80])).
% 1.39/0.57  fof(f80,plain,(
% 1.39/0.57    sP0(sK1,sK4,sK2)),
% 1.39/0.57    inference(resolution,[],[f55,f40])).
% 1.39/0.57  fof(f55,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f36])).
% 1.39/0.57  fof(f36,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(nnf_transformation,[],[f29])).
% 1.39/0.57  fof(f29,plain,(
% 1.39/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(definition_folding,[],[f23,f28])).
% 1.39/0.57  fof(f28,plain,(
% 1.39/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.39/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.39/0.57  fof(f23,plain,(
% 1.39/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(flattening,[],[f22])).
% 1.39/0.58  fof(f22,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.58    inference(ennf_transformation,[],[f8])).
% 1.39/0.58  fof(f8,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.58  fof(f51,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.39/0.58    inference(cnf_transformation,[],[f35])).
% 1.39/0.58  fof(f35,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.39/0.58    inference(rectify,[],[f34])).
% 1.39/0.58  fof(f34,plain,(
% 1.39/0.58    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.39/0.58    inference(nnf_transformation,[],[f28])).
% 1.39/0.58  fof(f43,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f16])).
% 1.39/0.58  fof(f16,plain,(
% 1.39/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.39/0.58    inference(flattening,[],[f15])).
% 1.39/0.58  fof(f15,plain,(
% 1.39/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.58    inference(ennf_transformation,[],[f3])).
% 1.39/0.58  fof(f3,axiom,(
% 1.39/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.39/0.58  fof(f102,plain,(
% 1.39/0.58    ~r2_relset_1(sK1,sK2,k7_relat_1(sK4,sK3),sK4)),
% 1.39/0.58    inference(backward_demodulation,[],[f42,f99])).
% 1.39/0.58  fof(f99,plain,(
% 1.39/0.58    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0)) )),
% 1.39/0.58    inference(resolution,[],[f98,f40])).
% 1.39/0.58  fof(f98,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)) )),
% 1.39/0.58    inference(resolution,[],[f58,f38])).
% 1.39/0.58  fof(f38,plain,(
% 1.39/0.58    v1_funct_1(sK4)),
% 1.39/0.58    inference(cnf_transformation,[],[f31])).
% 1.39/0.58  fof(f58,plain,(
% 1.39/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f25])).
% 1.39/0.58  fof(f25,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.39/0.58    inference(flattening,[],[f24])).
% 1.39/0.58  fof(f24,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.39/0.58    inference(ennf_transformation,[],[f9])).
% 1.39/0.58  fof(f9,axiom,(
% 1.39/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.39/0.58  fof(f42,plain,(
% 1.39/0.58    ~r2_relset_1(sK1,sK2,k2_partfun1(sK1,sK2,sK4,sK3),sK4)),
% 1.39/0.58    inference(cnf_transformation,[],[f31])).
% 1.39/0.58  fof(f85,plain,(
% 1.39/0.58    r2_relset_1(sK1,sK2,sK4,sK4)),
% 1.39/0.58    inference(resolution,[],[f69,f40])).
% 1.39/0.58  fof(f69,plain,(
% 1.39/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.39/0.58    inference(duplicate_literal_removal,[],[f68])).
% 1.39/0.58  fof(f68,plain,(
% 1.39/0.58    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.58    inference(equality_resolution,[],[f60])).
% 1.39/0.58  fof(f60,plain,(
% 1.39/0.58    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.58    inference(cnf_transformation,[],[f37])).
% 1.39/0.58  fof(f37,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.58    inference(nnf_transformation,[],[f27])).
% 1.39/0.58  fof(f27,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.58    inference(flattening,[],[f26])).
% 1.39/0.58  fof(f26,plain,(
% 1.39/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.39/0.58    inference(ennf_transformation,[],[f7])).
% 1.39/0.58  fof(f7,axiom,(
% 1.39/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.39/0.58  fof(f128,plain,(
% 1.39/0.58    ~r2_relset_1(sK1,k1_xboole_0,sK4,sK4)),
% 1.39/0.58    inference(backward_demodulation,[],[f111,f124])).
% 1.39/0.58  fof(f124,plain,(
% 1.39/0.58    ( ! [X0] : (sK4 = k7_relat_1(sK4,X0)) )),
% 1.39/0.58    inference(subsumption_resolution,[],[f78,f117])).
% 1.39/0.58  fof(f117,plain,(
% 1.39/0.58    ( ! [X1] : (v4_relat_1(sK4,X1)) )),
% 1.39/0.58    inference(resolution,[],[f112,f76])).
% 1.39/0.58  fof(f76,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 1.39/0.58    inference(superposition,[],[f50,f61])).
% 1.39/0.58  fof(f61,plain,(
% 1.39/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.58    inference(equality_resolution,[],[f47])).
% 1.39/0.58  fof(f47,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.39/0.58    inference(cnf_transformation,[],[f33])).
% 1.39/0.58  fof(f33,plain,(
% 1.39/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.39/0.58    inference(flattening,[],[f32])).
% 1.39/0.58  fof(f32,plain,(
% 1.39/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.39/0.58    inference(nnf_transformation,[],[f1])).
% 1.39/0.58  fof(f1,axiom,(
% 1.39/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.58  fof(f50,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f21])).
% 1.39/0.58  fof(f21,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.58    inference(ennf_transformation,[],[f12])).
% 1.39/0.58  fof(f12,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.39/0.58    inference(pure_predicate_removal,[],[f5])).
% 1.39/0.58  fof(f5,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.39/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.39/0.58  fof(f112,plain,(
% 1.39/0.58    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 1.39/0.58    inference(forward_demodulation,[],[f106,f61])).
% 1.39/0.58  fof(f106,plain,(
% 1.39/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.39/0.58    inference(backward_demodulation,[],[f40,f104])).
% 1.39/0.58  fof(f78,plain,(
% 1.39/0.58    ( ! [X0] : (~v4_relat_1(sK4,X0) | sK4 = k7_relat_1(sK4,X0)) )),
% 1.39/0.58    inference(resolution,[],[f44,f72])).
% 1.39/0.58  fof(f44,plain,(
% 1.39/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.39/0.58    inference(cnf_transformation,[],[f18])).
% 1.39/0.58  fof(f18,plain,(
% 1.39/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.39/0.58    inference(flattening,[],[f17])).
% 1.39/0.58  % (29232)Refutation not found, incomplete strategy% (29232)------------------------------
% 1.39/0.58  % (29232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (29232)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (29232)Memory used [KB]: 6268
% 1.39/0.58  % (29232)Time elapsed: 0.138 s
% 1.39/0.58  % (29232)------------------------------
% 1.39/0.58  % (29232)------------------------------
% 1.39/0.58  % (29225)Refutation not found, incomplete strategy% (29225)------------------------------
% 1.39/0.58  % (29225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (29225)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (29225)Memory used [KB]: 10618
% 1.39/0.58  % (29225)Time elapsed: 0.137 s
% 1.39/0.58  % (29225)------------------------------
% 1.39/0.58  % (29225)------------------------------
% 1.39/0.59  fof(f17,plain,(
% 1.39/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.39/0.59    inference(ennf_transformation,[],[f2])).
% 1.39/0.59  fof(f2,axiom,(
% 1.39/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.39/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.39/0.59  fof(f111,plain,(
% 1.39/0.59    ~r2_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,sK3),sK4)),
% 1.39/0.59    inference(backward_demodulation,[],[f102,f104])).
% 1.39/0.59  % SZS output end Proof for theBenchmark
% 1.39/0.59  % (29222)------------------------------
% 1.39/0.59  % (29222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.59  % (29222)Termination reason: Refutation
% 1.39/0.59  
% 1.39/0.59  % (29222)Memory used [KB]: 6268
% 1.39/0.59  % (29222)Time elapsed: 0.113 s
% 1.39/0.59  % (29222)------------------------------
% 1.39/0.59  % (29222)------------------------------
% 1.39/0.59  % (29218)Success in time 0.214 s
%------------------------------------------------------------------------------
