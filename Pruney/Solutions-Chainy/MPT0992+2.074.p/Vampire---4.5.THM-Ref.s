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
% DateTime   : Thu Dec  3 13:03:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 (2153 expanded)
%              Number of leaves         :   19 ( 517 expanded)
%              Depth                    :   28
%              Number of atoms          :  423 (10987 expanded)
%              Number of equality atoms :  138 (2651 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2845,plain,(
    $false ),
    inference(resolution,[],[f2842,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f2842,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f2123,f678])).

fof(f678,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(resolution,[],[f672,f224])).

fof(f224,plain,(
    ! [X0,X1] : sP0(X0,k1_xboole_0,X1) ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f672,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(trivial_inequality_removal,[],[f670])).

fof(f670,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ sP0(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f87,f344])).

fof(f344,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f339,f316])).

fof(f316,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f314,f103])).

fof(f103,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f65,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f314,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(k1_xboole_0) = X0 ) ),
    inference(forward_demodulation,[],[f307,f101])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f100,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f100,plain,(
    ! [X3] : r1_tarski(k7_relat_1(k1_xboole_0,X3),k1_xboole_0) ),
    inference(resolution,[],[f60,f96])).

fof(f96,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f59,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f307,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_xboole_0))
      | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ) ),
    inference(resolution,[],[f61,f96])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f339,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f70,f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f87,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP0(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f2123,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2122,f485])).

fof(f485,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(resolution,[],[f482,f58])).

fof(f482,plain,(
    r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f480,f216])).

fof(f216,plain,(
    ! [X0] : sP5(k7_relat_1(sK4,X0),sK2) ),
    inference(resolution,[],[f213,f174])).

fof(f174,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X3,X2))
      | sP5(X1,X2) ) ),
    inference(resolution,[],[f92,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | sP5(X3,X2) ) ),
    inference(cnf_transformation,[],[f92_D])).

fof(f92_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    <=> ~ sP5(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f213,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f211,f83])).

fof(f211,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k7_relat_1(sK4,X3))
      | r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) ) ),
    inference(resolution,[],[f162,f119])).

fof(f119,plain,(
    ! [X1] : r1_tarski(k7_relat_1(sK4,X1),sK4) ),
    inference(resolution,[],[f114,f60])).

fof(f114,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f107,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f40])).

fof(f40,plain,
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

% (3102)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f57,f59])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f162,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,sK4)
      | r1_tarski(X2,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f156,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f156,plain,(
    ! [X10] :
      ( r1_tarski(X10,k2_zfmisc_1(sK1,sK2))
      | ~ r1_tarski(X10,sK4) ) ),
    inference(resolution,[],[f78,f104])).

fof(f104,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f65,f52])).

fof(f480,plain,(
    ! [X1] :
      ( ~ sP5(k7_relat_1(sK4,k1_xboole_0),X1)
      | r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f474,f86])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f474,plain,(
    ! [X1] :
      ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,X1))
      | ~ sP5(k7_relat_1(sK4,k1_xboole_0),X1) ) ),
    inference(superposition,[],[f394,f320])).

fof(f320,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) ),
    inference(resolution,[],[f313,f103])).

fof(f313,plain,(
    ! [X17] :
      ( ~ r1_tarski(X17,k1_relat_1(sK4))
      | k1_relat_1(k7_relat_1(sK4,X17)) = X17 ) ),
    inference(resolution,[],[f61,f114])).

fof(f394,plain,(
    ! [X8,X9] :
      ( r1_tarski(X8,k2_zfmisc_1(k1_relat_1(X8),X9))
      | ~ sP5(X8,X9) ) ),
    inference(resolution,[],[f380,f65])).

% (3093)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f380,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | ~ sP5(X0,X1) ) ),
    inference(resolution,[],[f93,f83])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ sP5(X3,X2) ) ),
    inference(general_splitting,[],[f79,f92_D])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f2122,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2121,f2102])).

fof(f2102,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f1978,f58])).

fof(f1978,plain,(
    r1_tarski(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f1860])).

fof(f1860,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f54,f1858])).

fof(f1858,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1857,f216])).

fof(f1857,plain,
    ( ~ sP5(k7_relat_1(sK4,sK3),sK2)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f1706,f1856])).

fof(f1856,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)
    | ~ sP5(k7_relat_1(sK4,sK3),sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1839,f1579])).

% (3091)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f1579,plain,(
    ! [X10] :
      ( r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,X10))
      | ~ sP5(k7_relat_1(sK4,sK3),X10)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f394,f1563])).

fof(f1563,plain,
    ( sK3 = k1_relat_1(k7_relat_1(sK4,sK3))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1476,f53])).

fof(f1476,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_relat_1(k7_relat_1(sK4,X0)) = X0
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f313,f1472])).

fof(f1472,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f51,f1471])).

fof(f1471,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f1457,f340])).

fof(f340,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f70,f52])).

fof(f1457,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f71,f225])).

fof(f225,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f75,f52])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f51,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f1839,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,sK2))
    | ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) ),
    inference(forward_demodulation,[],[f1835,f1825])).

fof(f1825,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0) ),
    inference(resolution,[],[f1819,f52])).

fof(f1819,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2) ) ),
    inference(resolution,[],[f80,f50])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f1835,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) ),
    inference(backward_demodulation,[],[f1131,f1825])).

fof(f1131,plain,
    ( ~ r1_tarski(k2_partfun1(sK1,sK2,sK4,sK3),k2_zfmisc_1(sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) ),
    inference(resolution,[],[f608,f66])).

fof(f608,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) ),
    inference(subsumption_resolution,[],[f55,f603])).

fof(f603,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) ),
    inference(resolution,[],[f441,f52])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,sK4,X2)) ) ),
    inference(resolution,[],[f81,f50])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f55,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1706,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f1705])).

fof(f1705,plain,
    ( v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f1691,f1563])).

fof(f1691,plain,(
    ! [X4] :
      ( v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),sK2)
      | k1_xboole_0 = sK2 ) ),
    inference(global_subsumption,[],[f454,f1687])).

fof(f1687,plain,(
    ! [X4] :
      ( v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),sK2)
      | k1_xboole_0 = sK2
      | ~ sP0(k1_relat_1(k7_relat_1(sK4,X4)),k7_relat_1(sK4,X4),sK2) ) ),
    inference(trivial_inequality_removal,[],[f1668])).

fof(f1668,plain,(
    ! [X4] :
      ( k1_relat_1(k7_relat_1(sK4,X4)) != k1_relat_1(k7_relat_1(sK4,X4))
      | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),sK2)
      | k1_xboole_0 = sK2
      | ~ sP0(k1_relat_1(k7_relat_1(sK4,X4)),k7_relat_1(sK4,X4),sK2) ) ),
    inference(superposition,[],[f73,f654])).

fof(f654,plain,(
    ! [X8] : k1_relat_1(k7_relat_1(sK4,X8)) = k1_relset_1(k1_relat_1(k7_relat_1(sK4,X8)),sK2,k7_relat_1(sK4,X8)) ),
    inference(resolution,[],[f390,f216])).

fof(f390,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | k1_relat_1(X0) = k1_relset_1(k1_relat_1(X0),X1,X0) ) ),
    inference(resolution,[],[f380,f70])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f454,plain,(
    ! [X8] : sP0(k1_relat_1(k7_relat_1(sK4,X8)),k7_relat_1(sK4,X8),sK2) ),
    inference(resolution,[],[f391,f216])).

fof(f391,plain,(
    ! [X2,X3] :
      ( ~ sP5(X2,X3)
      | sP0(k1_relat_1(X2),X2,X3) ) ),
    inference(resolution,[],[f380,f75])).

fof(f54,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f2121,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK4,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2119,f485])).

fof(f2119,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK4,sK3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f2099,f2102])).

fof(f2099,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,sK3),k1_xboole_0)
    | ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2098,f85])).

fof(f2098,plain,
    ( ~ r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,k1_xboole_0))
    | ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1976,f1858])).

fof(f1976,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f1839,f1858])).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 20:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (3099)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (3097)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (3096)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (3089)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (3112)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (3088)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (3090)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (3104)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (3106)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (3098)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (3103)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (3087)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (3100)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (3092)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (3108)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (3107)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (3109)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (3101)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (3099)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f2845,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(resolution,[],[f2842,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f2842,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f2123,f678])).
% 0.21/0.54  fof(f678,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f672,f224])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP0(X0,k1_xboole_0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f75,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(definition_folding,[],[f29,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f672,plain,(
% 0.21/0.54    ( ! [X0] : (~sP0(k1_xboole_0,k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f670])).
% 0.21/0.54  fof(f670,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~sP0(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.21/0.54    inference(superposition,[],[f87,f344])).
% 0.21/0.54  fof(f344,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f339,f316])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f314,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f65,f56])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(k1_xboole_0) = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f307,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f100,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X3] : (r1_tarski(k7_relat_1(k1_xboole_0,X3),k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f60,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    v1_relat_1(k1_xboole_0)),
% 0.21/0.54    inference(superposition,[],[f59,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k7_relat_1(X1,X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_xboole_0)) | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0) )),
% 0.21/0.54    inference(resolution,[],[f61,f96])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f70,f56])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP0(k1_xboole_0,X1,X2)) )),
% 0.21/0.54    inference(equality_resolution,[],[f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f38])).
% 0.21/0.54  fof(f2123,plain,(
% 0.21/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f2122,f485])).
% 0.21/0.54  fof(f485,plain,(
% 0.21/0.54    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f482,f58])).
% 0.21/0.54  fof(f482,plain,(
% 0.21/0.54    r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)),
% 0.21/0.54    inference(resolution,[],[f480,f216])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ( ! [X0] : (sP5(k7_relat_1(sK4,X0),sK2)) )),
% 0.21/0.54    inference(resolution,[],[f213,f174])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (~r1_tarski(X1,k2_zfmisc_1(X3,X2)) | sP5(X1,X2)) )),
% 0.21/0.54    inference(resolution,[],[f92,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | sP5(X3,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f92_D])).
% 0.21/0.54  fof(f92_D,plain,(
% 0.21/0.54    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) <=> ~sP5(X3,X2)) )),
% 0.21/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k7_relat_1(sK4,X0),k2_zfmisc_1(sK1,sK2))) )),
% 0.21/0.54    inference(resolution,[],[f211,f83])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r1_tarski(X2,k7_relat_1(sK4,X3)) | r1_tarski(X2,k2_zfmisc_1(sK1,sK2))) )),
% 0.21/0.54    inference(resolution,[],[f162,f119])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k7_relat_1(sK4,X1),sK4)) )),
% 0.21/0.54    inference(resolution,[],[f114,f60])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    v1_relat_1(sK4)),
% 0.21/0.54    inference(resolution,[],[f107,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    (~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (3102)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f17])).
% 0.21/0.54  fof(f17,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 0.21/0.54    inference(resolution,[],[f57,f59])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r1_tarski(X1,sK4) | r1_tarski(X2,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X2,X1)) )),
% 0.21/0.54    inference(resolution,[],[f156,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X10] : (r1_tarski(X10,k2_zfmisc_1(sK1,sK2)) | ~r1_tarski(X10,sK4)) )),
% 0.21/0.54    inference(resolution,[],[f78,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.54    inference(resolution,[],[f65,f52])).
% 0.21/0.54  fof(f480,plain,(
% 0.21/0.54    ( ! [X1] : (~sP5(k7_relat_1(sK4,k1_xboole_0),X1) | r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f474,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f474,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(k7_relat_1(sK4,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,X1)) | ~sP5(k7_relat_1(sK4,k1_xboole_0),X1)) )),
% 0.21/0.54    inference(superposition,[],[f394,f320])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0))),
% 0.21/0.54    inference(resolution,[],[f313,f103])).
% 0.21/0.54  fof(f313,plain,(
% 0.21/0.54    ( ! [X17] : (~r1_tarski(X17,k1_relat_1(sK4)) | k1_relat_1(k7_relat_1(sK4,X17)) = X17) )),
% 0.21/0.54    inference(resolution,[],[f61,f114])).
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    ( ! [X8,X9] : (r1_tarski(X8,k2_zfmisc_1(k1_relat_1(X8),X9)) | ~sP5(X8,X9)) )),
% 0.21/0.54    inference(resolution,[],[f380,f65])).
% 0.21/0.54  % (3093)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | ~sP5(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f93,f83])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~sP5(X3,X2)) )),
% 0.21/0.54    inference(general_splitting,[],[f79,f92_D])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.54  fof(f2122,plain,(
% 0.21/0.54    ~r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.54    inference(forward_demodulation,[],[f2121,f2102])).
% 0.21/0.54  fof(f2102,plain,(
% 0.21/0.54    k1_xboole_0 = sK3),
% 0.21/0.54    inference(resolution,[],[f1978,f58])).
% 0.21/0.54  fof(f1978,plain,(
% 0.21/0.54    r1_tarski(sK3,k1_xboole_0)),
% 0.21/0.54    inference(backward_demodulation,[],[f53,f1860])).
% 0.21/0.54  fof(f1860,plain,(
% 0.21/0.54    k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f54,f1858])).
% 0.21/0.54  fof(f1858,plain,(
% 0.21/0.54    k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f1857,f216])).
% 0.21/0.54  fof(f1857,plain,(
% 0.21/0.54    ~sP5(k7_relat_1(sK4,sK3),sK2) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(global_subsumption,[],[f1706,f1856])).
% 0.21/0.54  fof(f1856,plain,(
% 0.21/0.54    ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) | ~sP5(k7_relat_1(sK4,sK3),sK2) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f1839,f1579])).
% 0.21/0.54  % (3091)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  fof(f1579,plain,(
% 0.21/0.54    ( ! [X10] : (r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,X10)) | ~sP5(k7_relat_1(sK4,sK3),X10) | k1_xboole_0 = sK2) )),
% 0.21/0.54    inference(superposition,[],[f394,f1563])).
% 0.21/0.54  fof(f1563,plain,(
% 0.21/0.54    sK3 = k1_relat_1(k7_relat_1(sK4,sK3)) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f1476,f53])).
% 0.21/0.55  fof(f1476,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_relat_1(k7_relat_1(sK4,X0)) = X0 | k1_xboole_0 = sK2) )),
% 0.21/0.55    inference(superposition,[],[f313,f1472])).
% 0.21/0.55  fof(f1472,plain,(
% 0.21/0.55    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.21/0.55    inference(global_subsumption,[],[f51,f1471])).
% 0.21/0.55  fof(f1471,plain,(
% 0.21/0.55    sK1 = k1_relat_1(sK4) | ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2),
% 0.21/0.55    inference(forward_demodulation,[],[f1457,f340])).
% 0.21/0.55  fof(f340,plain,(
% 0.21/0.55    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 0.21/0.55    inference(resolution,[],[f70,f52])).
% 0.21/0.55  fof(f1457,plain,(
% 0.21/0.55    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.21/0.55    inference(resolution,[],[f71,f225])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    sP0(sK1,sK4,sK2)),
% 0.21/0.55    inference(resolution,[],[f75,f52])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f1839,plain,(
% 0.21/0.55    ~r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,sK2)) | ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2)),
% 0.21/0.55    inference(forward_demodulation,[],[f1835,f1825])).
% 0.21/0.55  fof(f1825,plain,(
% 0.21/0.55    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK1,sK2,sK4,X0)) )),
% 0.21/0.55    inference(resolution,[],[f1819,f52])).
% 0.21/0.55  fof(f1819,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2)) )),
% 0.21/0.55    inference(resolution,[],[f80,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    v1_funct_1(sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.55  fof(f1835,plain,(
% 0.21/0.55    ~r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f1131,f1825])).
% 0.21/0.55  fof(f1131,plain,(
% 0.21/0.55    ~r1_tarski(k2_partfun1(sK1,sK2,sK4,sK3),k2_zfmisc_1(sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)),
% 0.21/0.55    inference(resolution,[],[f608,f66])).
% 0.21/0.55  fof(f608,plain,(
% 0.21/0.55    ~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f55,f603])).
% 0.21/0.55  fof(f603,plain,(
% 0.21/0.55    ( ! [X0] : (v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0))) )),
% 0.21/0.55    inference(resolution,[],[f441,f52])).
% 0.21/0.55  fof(f441,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))) )),
% 0.21/0.55    inference(resolution,[],[f81,f50])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.55    inference(flattening,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f1706,plain,(
% 0.21/0.55    v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) | k1_xboole_0 = sK2),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f1705])).
% 0.21/0.55  fof(f1705,plain,(
% 0.21/0.55    v1_funct_2(k7_relat_1(sK4,sK3),sK3,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.21/0.55    inference(superposition,[],[f1691,f1563])).
% 0.21/0.55  fof(f1691,plain,(
% 0.21/0.55    ( ! [X4] : (v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),sK2) | k1_xboole_0 = sK2) )),
% 0.21/0.55    inference(global_subsumption,[],[f454,f1687])).
% 0.21/0.55  fof(f1687,plain,(
% 0.21/0.55    ( ! [X4] : (v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),sK2) | k1_xboole_0 = sK2 | ~sP0(k1_relat_1(k7_relat_1(sK4,X4)),k7_relat_1(sK4,X4),sK2)) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f1668])).
% 0.21/0.55  fof(f1668,plain,(
% 0.21/0.55    ( ! [X4] : (k1_relat_1(k7_relat_1(sK4,X4)) != k1_relat_1(k7_relat_1(sK4,X4)) | v1_funct_2(k7_relat_1(sK4,X4),k1_relat_1(k7_relat_1(sK4,X4)),sK2) | k1_xboole_0 = sK2 | ~sP0(k1_relat_1(k7_relat_1(sK4,X4)),k7_relat_1(sK4,X4),sK2)) )),
% 0.21/0.55    inference(superposition,[],[f73,f654])).
% 0.21/0.55  fof(f654,plain,(
% 0.21/0.55    ( ! [X8] : (k1_relat_1(k7_relat_1(sK4,X8)) = k1_relset_1(k1_relat_1(k7_relat_1(sK4,X8)),sK2,k7_relat_1(sK4,X8))) )),
% 0.21/0.55    inference(resolution,[],[f390,f216])).
% 0.21/0.55  fof(f390,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sP5(X0,X1) | k1_relat_1(X0) = k1_relset_1(k1_relat_1(X0),X1,X0)) )),
% 0.21/0.55    inference(resolution,[],[f380,f70])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f48])).
% 0.21/0.55  fof(f454,plain,(
% 0.21/0.55    ( ! [X8] : (sP0(k1_relat_1(k7_relat_1(sK4,X8)),k7_relat_1(sK4,X8),sK2)) )),
% 0.21/0.55    inference(resolution,[],[f391,f216])).
% 0.21/0.55  fof(f391,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~sP5(X2,X3) | sP0(k1_relat_1(X2),X2,X3)) )),
% 0.21/0.55    inference(resolution,[],[f380,f75])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    r1_tarski(sK3,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f2121,plain,(
% 0.21/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r1_tarski(k7_relat_1(sK4,sK3),k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f2119,f485])).
% 0.21/0.55  fof(f2119,plain,(
% 0.21/0.55    ~v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~r1_tarski(k7_relat_1(sK4,sK3),k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f2099,f2102])).
% 0.21/0.55  fof(f2099,plain,(
% 0.21/0.55    ~r1_tarski(k7_relat_1(sK4,sK3),k1_xboole_0) | ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f2098,f85])).
% 0.21/0.55  fof(f2098,plain,(
% 0.21/0.55    ~r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,k1_xboole_0)) | ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f1976,f1858])).
% 0.21/0.55  fof(f1976,plain,(
% 0.21/0.55    ~v1_funct_2(k7_relat_1(sK4,sK3),sK3,k1_xboole_0) | ~r1_tarski(k7_relat_1(sK4,sK3),k2_zfmisc_1(sK3,sK2))),
% 0.21/0.55    inference(backward_demodulation,[],[f1839,f1858])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (3099)------------------------------
% 0.21/0.55  % (3099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3099)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (3099)Memory used [KB]: 8187
% 0.21/0.55  % (3099)Time elapsed: 0.100 s
% 0.21/0.55  % (3099)------------------------------
% 0.21/0.55  % (3099)------------------------------
% 0.21/0.55  % (3105)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (3084)Success in time 0.183 s
%------------------------------------------------------------------------------
