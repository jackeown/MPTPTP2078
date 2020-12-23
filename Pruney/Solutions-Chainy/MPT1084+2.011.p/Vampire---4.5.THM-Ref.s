%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:20 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 259 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  258 (1194 expanded)
%              Number of equality atoms :   70 ( 232 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(subsumption_resolution,[],[f197,f189])).

fof(f189,plain,(
    r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f188,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f187,f31])).

fof(f31,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,sK1,sK1) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK1,X0,X1)
      | ~ v1_funct_2(sK1,X0,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,sK1,sK1) ) ),
    inference(resolution,[],[f127,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_2(sK1,X1,X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(resolution,[],[f55,f30])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f197,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f33,f196])).

fof(f196,plain,(
    sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f195,f102])).

fof(f102,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK3(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f101,f73])).

fof(f73,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f101,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK3(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f100,f30])).

fof(f100,plain,
    ( sK3(sK0,sK1) != k1_funct_1(sK1,sK3(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(superposition,[],[f65,f90])).

fof(f90,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f77,f89])).

fof(f89,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f88,f32])).

fof(f88,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f87,f31])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK1,X0,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,sK1) = X0 ) ),
    inference(resolution,[],[f51,f30])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f77,plain,(
    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f65,plain,(
    ! [X1] :
      ( sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f58])).

% (2959)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f48,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f195,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,
    ( sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1))
    | sK1 = k6_partfun1(sK0)
    | sK1 = k6_partfun1(sK0) ),
    inference(superposition,[],[f134,f103])).

fof(f103,plain,
    ( sK3(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK3(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(resolution,[],[f96,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = X0 ) ),
    inference(resolution,[],[f29,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f29,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | k3_funct_2(sK0,sK0,sK1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f95,f73])).

fof(f95,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0) ),
    inference(superposition,[],[f66,f90])).

fof(f66,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK3(X0,X1),X0)
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK3(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f134,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK3(sK0,sK1))
    | sK1 = k6_partfun1(sK0) ),
    inference(resolution,[],[f131,f96])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f130,f67])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f129,f32])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f128,f34])).

fof(f34,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f128,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f126,f31])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK1,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,X0)
      | k3_funct_2(X0,X1,sK1,X2) = k1_funct_1(sK1,X2) ) ),
    inference(resolution,[],[f54,f30])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f33,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.40/0.55  % (2962)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.56  % (2962)Refutation found. Thanks to Tanya!
% 1.40/0.56  % SZS status Theorem for theBenchmark
% 1.40/0.57  % (2970)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.58/0.57  % (2958)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.57  % (2978)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f198,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(subsumption_resolution,[],[f197,f189])).
% 1.58/0.57  fof(f189,plain,(
% 1.58/0.57    r2_funct_2(sK0,sK0,sK1,sK1)),
% 1.58/0.57    inference(subsumption_resolution,[],[f188,f32])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f15,plain,(
% 1.58/0.57    ? [X0] : (? [X1] : (~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) & ~v1_xboole_0(X0))),
% 1.58/0.57    inference(flattening,[],[f14])).
% 1.58/0.57  fof(f14,plain,(
% 1.58/0.57    ? [X0] : (? [X1] : ((~r2_funct_2(X0,X0,X1,k6_partfun1(X0)) & ! [X2] : (k3_funct_2(X0,X0,X1,X2) = X2 | ~m1_subset_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))) & ~v1_xboole_0(X0))),
% 1.58/0.57    inference(ennf_transformation,[],[f13])).
% 1.58/0.57  fof(f13,negated_conjecture,(
% 1.58/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.58/0.57    inference(negated_conjecture,[],[f12])).
% 1.58/0.57  fof(f12,conjecture,(
% 1.58/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (! [X2] : (m1_subset_1(X2,X0) => k3_funct_2(X0,X0,X1,X2) = X2) => r2_funct_2(X0,X0,X1,k6_partfun1(X0)))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).
% 1.58/0.57  fof(f188,plain,(
% 1.58/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | r2_funct_2(sK0,sK0,sK1,sK1)),
% 1.58/0.57    inference(resolution,[],[f187,f31])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    v1_funct_2(sK1,sK0,sK0)),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f187,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,sK1,sK1)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f186])).
% 1.58/0.57  fof(f186,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK1,X0,X1) | ~v1_funct_2(sK1,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,sK1,sK1)) )),
% 1.58/0.57    inference(resolution,[],[f127,f30])).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    v1_funct_1(sK1)),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f127,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_2(sK1,X1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0)) )),
% 1.58/0.57    inference(resolution,[],[f55,f30])).
% 1.58/0.57  fof(f55,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.58/0.57    inference(flattening,[],[f27])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.58/0.57    inference(ennf_transformation,[],[f10])).
% 1.58/0.57  fof(f10,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.58/0.57  fof(f197,plain,(
% 1.58/0.57    ~r2_funct_2(sK0,sK0,sK1,sK1)),
% 1.58/0.57    inference(backward_demodulation,[],[f33,f196])).
% 1.58/0.57  fof(f196,plain,(
% 1.58/0.57    sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(subsumption_resolution,[],[f195,f102])).
% 1.58/0.57  fof(f102,plain,(
% 1.58/0.57    sK3(sK0,sK1) != k1_funct_1(sK1,sK3(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(subsumption_resolution,[],[f101,f73])).
% 1.58/0.57  fof(f73,plain,(
% 1.58/0.57    v1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f52,f32])).
% 1.58/0.57  fof(f52,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.58/0.57  fof(f101,plain,(
% 1.58/0.57    sK3(sK0,sK1) != k1_funct_1(sK1,sK3(sK0,sK1)) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(subsumption_resolution,[],[f100,f30])).
% 1.58/0.57  fof(f100,plain,(
% 1.58/0.57    sK3(sK0,sK1) != k1_funct_1(sK1,sK3(sK0,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(superposition,[],[f65,f90])).
% 1.58/0.57  fof(f90,plain,(
% 1.58/0.57    sK0 = k1_relat_1(sK1)),
% 1.58/0.57    inference(backward_demodulation,[],[f77,f89])).
% 1.58/0.57  fof(f89,plain,(
% 1.58/0.57    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.58/0.57    inference(subsumption_resolution,[],[f88,f32])).
% 1.58/0.57  fof(f88,plain,(
% 1.58/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.58/0.57    inference(resolution,[],[f87,f31])).
% 1.58/0.57  fof(f87,plain,(
% 1.58/0.57    ( ! [X0] : (~v1_funct_2(sK1,X0,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,sK1) = X0) )),
% 1.58/0.57    inference(resolution,[],[f51,f30])).
% 1.58/0.57  fof(f51,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0) )),
% 1.58/0.57    inference(cnf_transformation,[],[f22])).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.58/0.57    inference(flattening,[],[f21])).
% 1.58/0.57  fof(f21,plain,(
% 1.58/0.57    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f11])).
% 1.58/0.57  fof(f11,axiom,(
% 1.58/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 1.58/0.57  fof(f77,plain,(
% 1.58/0.57    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 1.58/0.57    inference(resolution,[],[f53,f32])).
% 1.58/0.57  fof(f53,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f24])).
% 1.58/0.57  fof(f24,plain,(
% 1.58/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f6])).
% 1.58/0.57  fof(f6,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.58/0.57  fof(f65,plain,(
% 1.58/0.57    ( ! [X1] : (sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 1.58/0.57    inference(equality_resolution,[],[f58])).
% 1.58/0.57  % (2959)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.57  fof(f58,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_partfun1(X0) = X1) )),
% 1.58/0.57    inference(definition_unfolding,[],[f48,f36])).
% 1.58/0.57  fof(f36,plain,(
% 1.58/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f8])).
% 1.58/0.57  fof(f8,axiom,(
% 1.58/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.58/0.57  fof(f48,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k6_relat_1(X0) = X1) )),
% 1.58/0.57    inference(cnf_transformation,[],[f20])).
% 1.58/0.57  fof(f20,plain,(
% 1.58/0.57    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(flattening,[],[f19])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f4])).
% 1.58/0.57  fof(f4,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 1.58/0.57  fof(f195,plain,(
% 1.58/0.57    sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f190])).
% 1.58/0.57  fof(f190,plain,(
% 1.58/0.57    sK3(sK0,sK1) = k1_funct_1(sK1,sK3(sK0,sK1)) | sK1 = k6_partfun1(sK0) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(superposition,[],[f134,f103])).
% 1.58/0.57  fof(f103,plain,(
% 1.58/0.57    sK3(sK0,sK1) = k3_funct_2(sK0,sK0,sK1,sK3(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(resolution,[],[f96,f68])).
% 1.58/0.57  fof(f68,plain,(
% 1.58/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = X0) )),
% 1.58/0.57    inference(resolution,[],[f29,f67])).
% 1.58/0.57  fof(f67,plain,(
% 1.58/0.57    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.58/0.57    inference(subsumption_resolution,[],[f45,f42])).
% 1.58/0.57  fof(f42,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f18])).
% 1.58/0.57  fof(f18,plain,(
% 1.58/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.58/0.57    inference(ennf_transformation,[],[f2])).
% 1.58/0.57  fof(f2,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.58/0.57  fof(f29,plain,(
% 1.58/0.57    ( ! [X2] : (~m1_subset_1(X2,sK0) | k3_funct_2(sK0,sK0,sK1,X2) = X2) )),
% 1.58/0.57    inference(cnf_transformation,[],[f15])).
% 1.58/0.57  fof(f96,plain,(
% 1.58/0.57    r2_hidden(sK3(sK0,sK1),sK0) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(subsumption_resolution,[],[f95,f73])).
% 1.58/0.57  fof(f95,plain,(
% 1.58/0.57    r2_hidden(sK3(sK0,sK1),sK0) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(subsumption_resolution,[],[f93,f30])).
% 1.58/0.57  fof(f93,plain,(
% 1.58/0.57    r2_hidden(sK3(sK0,sK1),sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_partfun1(sK0)),
% 1.58/0.57    inference(superposition,[],[f66,f90])).
% 1.58/0.58  fof(f66,plain,(
% 1.58/0.58    ( ! [X1] : (r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_partfun1(k1_relat_1(X1)) = X1) )),
% 1.58/0.58    inference(equality_resolution,[],[f59])).
% 1.58/0.58  fof(f59,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_partfun1(X0) = X1) )),
% 1.58/0.58    inference(definition_unfolding,[],[f47,f36])).
% 1.58/0.58  fof(f47,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK3(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f20])).
% 1.58/0.58  fof(f134,plain,(
% 1.58/0.58    k1_funct_1(sK1,sK3(sK0,sK1)) = k3_funct_2(sK0,sK0,sK1,sK3(sK0,sK1)) | sK1 = k6_partfun1(sK0)),
% 1.58/0.58    inference(resolution,[],[f131,f96])).
% 1.58/0.58  fof(f131,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 1.58/0.58    inference(resolution,[],[f130,f67])).
% 1.58/0.58  fof(f130,plain,(
% 1.58/0.58    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 1.58/0.58    inference(subsumption_resolution,[],[f129,f32])).
% 1.58/0.58  fof(f129,plain,(
% 1.58/0.58    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 1.58/0.58    inference(subsumption_resolution,[],[f128,f34])).
% 1.58/0.58  fof(f34,plain,(
% 1.58/0.58    ~v1_xboole_0(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f15])).
% 1.58/0.58  fof(f128,plain,(
% 1.58/0.58    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK0,sK1,X0) = k1_funct_1(sK1,X0)) )),
% 1.58/0.58    inference(resolution,[],[f126,f31])).
% 1.58/0.58  fof(f126,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(sK1,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK1,X2) = k1_funct_1(sK1,X2)) )),
% 1.58/0.58    inference(resolution,[],[f54,f30])).
% 1.58/0.58  fof(f54,plain,(
% 1.58/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f26])).
% 1.58/0.58  fof(f26,plain,(
% 1.58/0.58    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 1.58/0.58    inference(flattening,[],[f25])).
% 1.58/0.58  fof(f25,plain,(
% 1.58/0.58    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f7])).
% 1.58/0.58  fof(f7,axiom,(
% 1.58/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 1.58/0.58  fof(f33,plain,(
% 1.58/0.58    ~r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))),
% 1.58/0.58    inference(cnf_transformation,[],[f15])).
% 1.58/0.58  % SZS output end Proof for theBenchmark
% 1.58/0.58  % (2962)------------------------------
% 1.58/0.58  % (2962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (2962)Termination reason: Refutation
% 1.58/0.58  
% 1.58/0.58  % (2962)Memory used [KB]: 6268
% 1.58/0.58  % (2962)Time elapsed: 0.137 s
% 1.58/0.58  % (2962)------------------------------
% 1.58/0.58  % (2962)------------------------------
% 1.58/0.58  % (2968)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.58  % (2955)Success in time 0.217 s
%------------------------------------------------------------------------------
