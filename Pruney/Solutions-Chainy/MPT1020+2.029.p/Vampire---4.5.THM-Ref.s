%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:44 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  178 (6894 expanded)
%              Number of leaves         :   20 (2059 expanded)
%              Depth                    :   49
%              Number of atoms          :  694 (56274 expanded)
%              Number of equality atoms :  179 (2862 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(subsumption_resolution,[],[f390,f201])).

fof(f201,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f96,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f96,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f91,f62])).

fof(f62,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f66,f65])).

fof(f65,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f390,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f334,f389])).

fof(f389,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f388,f63])).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f388,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f387,f64])).

fof(f64,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f387,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f386,f62])).

fof(f386,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f385,f64])).

fof(f385,plain,
    ( k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f384,f102])).

fof(f102,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f99,f62])).

fof(f99,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[],[f73,f91])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

% (1446)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f384,plain,
    ( k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f383,f299])).

fof(f299,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f298])).

fof(f298,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f297,f220])).

fof(f220,plain,(
    v5_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f103,f212])).

fof(f212,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f211,f103])).

fof(f211,plain,
    ( k1_xboole_0 = sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | sK0 != sK0
    | ~ v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f206,f131])).

fof(f131,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f130,f52])).

fof(f130,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f127,f54])).

fof(f54,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f127,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f206,plain,(
    ! [X0] :
      ( ~ v2_funct_2(sK1,X0)
      | k1_xboole_0 = sK0
      | sK0 != X0
      | ~ v5_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f205,f97])).

fof(f97,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f73,f55])).

fof(f205,plain,(
    ! [X0] :
      ( sK0 != X0
      | k1_xboole_0 = sK0
      | ~ v2_funct_2(sK1,X0)
      | ~ v5_relat_1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f197,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f197,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f196,f109])).

fof(f109,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f89,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f196,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | k1_xboole_0 = sK0
    | sK0 != k2_relat_1(sK1) ),
    inference(superposition,[],[f143,f194])).

fof(f194,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f193,f55])).

fof(f193,plain,
    ( sK0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f192,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f192,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK1)
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f191,f52])).

fof(f191,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f190,f53])).

fof(f53,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f190,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f189,f55])).

fof(f189,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f188,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f188,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f187,f57])).

fof(f57,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

% (1430)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f187,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f186,f59])).

fof(f186,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( sK2 = k2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK0 != k2_relset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f95,f90])).

fof(f90,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f60,f65])).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f94,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f79,f65])).

% (1419)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f81,f65])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f143,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f61,f142])).

fof(f142,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f141,f52])).

fof(f141,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f140,f53])).

fof(f140,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f137,f54])).

fof(f137,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f72,f55])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f61,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f75,f55])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f297,plain,
    ( k1_xboole_0 = sK1
    | ~ v5_relat_1(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f294,f97])).

fof(f294,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ v5_relat_1(sK1,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f291])).

fof(f291,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 != k1_xboole_0
    | ~ v5_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f116,f224])).

fof(f224,plain,(
    v2_funct_2(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f131,f212])).

fof(f116,plain,(
    ! [X4,X3] :
      ( ~ v2_funct_2(X3,X4)
      | k1_xboole_0 = X3
      | ~ v1_relat_1(X3)
      | k1_xboole_0 != X4
      | ~ v5_relat_1(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != X4
      | k1_xboole_0 = X3
      | ~ v1_relat_1(X3)
      | ~ v2_funct_2(X3,X4)
      | ~ v5_relat_1(X3,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f68,f70])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

% (1440)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f52,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f383,plain,
    ( k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f382,f301])).

fof(f301,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f124,f298])).

fof(f124,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f123,f52])).

fof(f123,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f120,f54])).

fof(f120,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f77,f55])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f382,plain,
    ( k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,
    ( k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)
    | ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f69,f378])).

fof(f378,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f377,f299])).

fof(f377,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f376,f96])).

fof(f376,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f356,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f356,plain,(
    k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f355,f299])).

fof(f355,plain,
    ( k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f354,f96])).

fof(f354,plain,
    ( k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f351])).

fof(f351,plain,
    ( k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(resolution,[],[f319,f335])).

fof(f335,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f312,f321])).

fof(f321,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f320,f221])).

fof(f221,plain,(
    v5_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f104,f212])).

fof(f104,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f75,f59])).

fof(f320,plain,
    ( k1_xboole_0 = sK2
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f293,f98])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f59])).

fof(f293,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f292])).

fof(f292,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 != k1_xboole_0
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f116,f225])).

fof(f225,plain,(
    v2_funct_2(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f133,f212])).

fof(f133,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f132,f56])).

fof(f132,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f128,f58])).

fof(f58,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f78,f59])).

fof(f312,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f238,f298])).

fof(f238,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f219,f62])).

fof(f219,plain,(
    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k6_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f90,f212])).

fof(f319,plain,(
    ! [X45,X43,X44,X42] :
      ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42),k1_xboole_0)
      | k1_xboole_0 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45)))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0)))
      | ~ v1_funct_1(X42)
      | ~ v1_funct_1(X44) ) ),
    inference(forward_demodulation,[],[f315,f298])).

fof(f315,plain,(
    ! [X45,X43,X44,X42] :
      ( k1_xboole_0 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42)
      | ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42),sK1)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45)))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0)))
      | ~ v1_funct_1(X42)
      | ~ v1_funct_1(X44) ) ),
    inference(backward_demodulation,[],[f247,f298])).

fof(f247,plain,(
    ! [X45,X43,X44,X42] :
      ( ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42),sK1)
      | sK1 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45)))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0)))
      | ~ v1_funct_1(X42)
      | ~ v1_funct_1(X44) ) ),
    inference(forward_demodulation,[],[f246,f212])).

fof(f246,plain,(
    ! [X45,X43,X44,X42] :
      ( sK1 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45)))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0)))
      | ~ v1_funct_1(X42)
      | ~ v1_funct_1(X44)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1) ) ),
    inference(forward_demodulation,[],[f245,f212])).

fof(f245,plain,(
    ! [X45,X43,X44,X42] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45)))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0)))
      | ~ v1_funct_1(X42)
      | ~ v1_funct_1(X44)
      | sK1 = k1_partfun1(sK0,X45,X43,sK0,X44,X42)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1) ) ),
    inference(forward_demodulation,[],[f234,f212])).

fof(f234,plain,(
    ! [X45,X43,X44,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0)))
      | ~ v1_funct_1(X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(sK0,X45)))
      | ~ v1_funct_1(X44)
      | sK1 = k1_partfun1(sK0,X45,X43,sK0,X44,X42)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1) ) ),
    inference(backward_demodulation,[],[f164,f212])).

fof(f164,plain,(
    ! [X45,X43,X44,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,sK0)))
      | ~ v1_funct_1(X42)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(sK0,X45)))
      | ~ v1_funct_1(X44)
      | sK1 = k1_partfun1(sK0,X45,X43,sK0,X44,X42)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1) ) ),
    inference(resolution,[],[f86,f134])).

% (1439)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | sK1 = X0
      | ~ r2_relset_1(sK0,sK0,X0,sK1) ) ),
    inference(resolution,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

% (1445)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f334,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f309,f321])).

fof(f309,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f229,f298])).

fof(f229,plain,(
    ~ r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1)) ),
    inference(backward_demodulation,[],[f143,f212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:47:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (1426)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.18/0.51  % (1421)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.18/0.51  % (1435)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.18/0.52  % (1424)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.52  % (1420)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.18/0.52  % (1429)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.18/0.52  % (1434)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.18/0.52  % (1428)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.18/0.53  % (1434)Refutation not found, incomplete strategy% (1434)------------------------------
% 1.18/0.53  % (1434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (1427)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.53  % (1425)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.53  % (1434)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (1434)Memory used [KB]: 10746
% 1.33/0.53  % (1434)Time elapsed: 0.108 s
% 1.33/0.53  % (1434)------------------------------
% 1.33/0.53  % (1434)------------------------------
% 1.33/0.53  % (1437)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.53  % (1431)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.53  % (1418)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.54  % (1444)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (1422)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.54  % (1443)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.54  % (1442)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.54  % (1423)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  % (1436)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.54  % (1438)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.55  % (1427)Refutation found. Thanks to Tanya!
% 1.33/0.55  % SZS status Theorem for theBenchmark
% 1.33/0.55  % (1447)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.55  % SZS output start Proof for theBenchmark
% 1.33/0.55  fof(f392,plain,(
% 1.33/0.55    $false),
% 1.33/0.55    inference(subsumption_resolution,[],[f390,f201])).
% 1.33/0.55  fof(f201,plain,(
% 1.33/0.55    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.33/0.55    inference(resolution,[],[f96,f89])).
% 1.33/0.55  fof(f89,plain,(
% 1.33/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f88])).
% 1.33/0.55  fof(f88,plain,(
% 1.33/0.55    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(equality_resolution,[],[f83])).
% 1.33/0.55  fof(f83,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f51])).
% 1.33/0.55  fof(f51,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(nnf_transformation,[],[f42])).
% 1.33/0.55  fof(f42,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(flattening,[],[f41])).
% 1.33/0.55  fof(f41,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.33/0.55    inference(ennf_transformation,[],[f8])).
% 1.33/0.55  fof(f8,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.33/0.55  fof(f96,plain,(
% 1.33/0.55    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.33/0.55    inference(superposition,[],[f91,f62])).
% 1.33/0.55  fof(f62,plain,(
% 1.33/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(cnf_transformation,[],[f3])).
% 1.33/0.55  fof(f3,axiom,(
% 1.33/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.33/0.55  fof(f91,plain,(
% 1.33/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.33/0.55    inference(forward_demodulation,[],[f66,f65])).
% 1.33/0.55  fof(f65,plain,(
% 1.33/0.55    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f15])).
% 1.33/0.55  fof(f15,axiom,(
% 1.33/0.55    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.33/0.55  fof(f66,plain,(
% 1.33/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f20])).
% 1.33/0.55  fof(f20,plain,(
% 1.33/0.55    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.33/0.55    inference(pure_predicate_removal,[],[f12])).
% 1.33/0.55  fof(f12,axiom,(
% 1.33/0.55    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.33/0.55  fof(f390,plain,(
% 1.33/0.55    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f334,f389])).
% 1.33/0.55  fof(f389,plain,(
% 1.33/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f388,f63])).
% 1.33/0.55  fof(f63,plain,(
% 1.33/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(cnf_transformation,[],[f1])).
% 1.33/0.55  fof(f1,axiom,(
% 1.33/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.33/0.55  fof(f388,plain,(
% 1.33/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(forward_demodulation,[],[f387,f64])).
% 1.33/0.55  fof(f64,plain,(
% 1.33/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(cnf_transformation,[],[f1])).
% 1.33/0.55  fof(f387,plain,(
% 1.33/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f386,f62])).
% 1.33/0.55  fof(f386,plain,(
% 1.33/0.55    k1_xboole_0 != k6_relat_1(k1_xboole_0) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(forward_demodulation,[],[f385,f64])).
% 1.33/0.55  fof(f385,plain,(
% 1.33/0.55    k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f384,f102])).
% 1.33/0.55  fof(f102,plain,(
% 1.33/0.55    v1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(superposition,[],[f99,f62])).
% 1.33/0.55  fof(f99,plain,(
% 1.33/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.33/0.55    inference(resolution,[],[f73,f91])).
% 1.33/0.55  fof(f73,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f32])).
% 1.33/0.55  fof(f32,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f5])).
% 1.33/0.55  % (1446)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.55  fof(f5,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.33/0.55  fof(f384,plain,(
% 1.33/0.55    k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f383,f299])).
% 1.33/0.55  fof(f299,plain,(
% 1.33/0.55    v1_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f52,f298])).
% 1.33/0.55  fof(f298,plain,(
% 1.33/0.55    k1_xboole_0 = sK1),
% 1.33/0.55    inference(subsumption_resolution,[],[f297,f220])).
% 1.33/0.55  fof(f220,plain,(
% 1.33/0.55    v5_relat_1(sK1,k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f103,f212])).
% 1.33/0.55  fof(f212,plain,(
% 1.33/0.55    k1_xboole_0 = sK0),
% 1.33/0.55    inference(subsumption_resolution,[],[f211,f103])).
% 1.33/0.55  fof(f211,plain,(
% 1.33/0.55    k1_xboole_0 = sK0 | ~v5_relat_1(sK1,sK0)),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f208])).
% 1.33/0.55  fof(f208,plain,(
% 1.33/0.55    k1_xboole_0 = sK0 | sK0 != sK0 | ~v5_relat_1(sK1,sK0)),
% 1.33/0.55    inference(resolution,[],[f206,f131])).
% 1.33/0.55  fof(f131,plain,(
% 1.33/0.55    v2_funct_2(sK1,sK0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f130,f52])).
% 1.33/0.55  fof(f130,plain,(
% 1.33/0.55    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f127,f54])).
% 1.33/0.55  fof(f54,plain,(
% 1.33/0.55    v3_funct_2(sK1,sK0,sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f49,plain,(
% 1.33/0.55    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.33/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f48,f47])).
% 1.33/0.55  fof(f47,plain,(
% 1.33/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f48,plain,(
% 1.33/0.55    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.33/0.55    introduced(choice_axiom,[])).
% 1.33/0.55  fof(f23,plain,(
% 1.33/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.33/0.55    inference(flattening,[],[f22])).
% 1.33/0.55  fof(f22,plain,(
% 1.33/0.55    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f19])).
% 1.33/0.55  fof(f19,negated_conjecture,(
% 1.33/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.33/0.55    inference(negated_conjecture,[],[f18])).
% 1.33/0.55  fof(f18,conjecture,(
% 1.33/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 1.33/0.55  fof(f127,plain,(
% 1.33/0.55    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0)),
% 1.33/0.55    inference(resolution,[],[f78,f55])).
% 1.33/0.55  fof(f55,plain,(
% 1.33/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f78,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f36])).
% 1.33/0.55  fof(f36,plain,(
% 1.33/0.55    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(flattening,[],[f35])).
% 1.33/0.55  fof(f35,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f9])).
% 1.33/0.55  fof(f9,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.33/0.55  fof(f206,plain,(
% 1.33/0.55    ( ! [X0] : (~v2_funct_2(sK1,X0) | k1_xboole_0 = sK0 | sK0 != X0 | ~v5_relat_1(sK1,X0)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f205,f97])).
% 1.33/0.55  fof(f97,plain,(
% 1.33/0.55    v1_relat_1(sK1)),
% 1.33/0.55    inference(resolution,[],[f73,f55])).
% 1.33/0.55  fof(f205,plain,(
% 1.33/0.55    ( ! [X0] : (sK0 != X0 | k1_xboole_0 = sK0 | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1)) )),
% 1.33/0.55    inference(superposition,[],[f197,f70])).
% 1.33/0.55  fof(f70,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f50])).
% 1.33/0.55  fof(f50,plain,(
% 1.33/0.55    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(nnf_transformation,[],[f29])).
% 1.33/0.55  fof(f29,plain,(
% 1.33/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.33/0.55    inference(flattening,[],[f28])).
% 1.33/0.55  fof(f28,plain,(
% 1.33/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f10])).
% 1.33/0.55  fof(f10,axiom,(
% 1.33/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.33/0.55  fof(f197,plain,(
% 1.33/0.55    sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0),
% 1.33/0.55    inference(subsumption_resolution,[],[f196,f109])).
% 1.33/0.55  fof(f109,plain,(
% 1.33/0.55    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.33/0.55    inference(resolution,[],[f89,f59])).
% 1.33/0.55  fof(f59,plain,(
% 1.33/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f196,plain,(
% 1.33/0.55    ~r2_relset_1(sK0,sK0,sK2,sK2) | k1_xboole_0 = sK0 | sK0 != k2_relat_1(sK1)),
% 1.33/0.55    inference(superposition,[],[f143,f194])).
% 1.33/0.55  fof(f194,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relat_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f193,f55])).
% 1.33/0.55  fof(f193,plain,(
% 1.33/0.55    sK0 != k2_relat_1(sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.33/0.55    inference(superposition,[],[f192,f74])).
% 1.33/0.55  fof(f74,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f33])).
% 1.33/0.55  fof(f33,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f7])).
% 1.33/0.55  fof(f7,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.33/0.55  fof(f192,plain,(
% 1.33/0.55    sK0 != k2_relset_1(sK0,sK0,sK1) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f191,f52])).
% 1.33/0.55  fof(f191,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f190,f53])).
% 1.33/0.55  fof(f53,plain,(
% 1.33/0.55    v1_funct_2(sK1,sK0,sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f190,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f189,f55])).
% 1.33/0.55  fof(f189,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f188,f56])).
% 1.33/0.55  fof(f56,plain,(
% 1.33/0.55    v1_funct_1(sK2)),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f188,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f187,f57])).
% 1.33/0.55  fof(f57,plain,(
% 1.33/0.55    v1_funct_2(sK2,sK0,sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  % (1430)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.55  fof(f187,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f186,f59])).
% 1.33/0.55  fof(f186,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f182])).
% 1.33/0.55  fof(f182,plain,(
% 1.33/0.55    sK2 = k2_funct_1(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK0 != k2_relset_1(sK0,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(resolution,[],[f95,f90])).
% 1.33/0.55  fof(f90,plain,(
% 1.33/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.33/0.55    inference(forward_demodulation,[],[f60,f65])).
% 1.33/0.55  fof(f60,plain,(
% 1.33/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f95,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.33/0.55    inference(subsumption_resolution,[],[f94,f93])).
% 1.33/0.55  fof(f93,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f79,f65])).
% 1.33/0.55  % (1419)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.55  fof(f79,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f38])).
% 1.33/0.55  fof(f38,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.33/0.55    inference(flattening,[],[f37])).
% 1.33/0.55  fof(f37,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.33/0.55    inference(ennf_transformation,[],[f16])).
% 1.33/0.55  fof(f16,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.33/0.55  fof(f94,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f81,f65])).
% 1.33/0.55  fof(f81,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f40])).
% 1.33/0.55  fof(f40,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.33/0.55    inference(flattening,[],[f39])).
% 1.33/0.55  fof(f39,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.33/0.55    inference(ennf_transformation,[],[f17])).
% 1.33/0.55  fof(f17,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.33/0.55  fof(f143,plain,(
% 1.33/0.55    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))),
% 1.33/0.55    inference(backward_demodulation,[],[f61,f142])).
% 1.33/0.55  fof(f142,plain,(
% 1.33/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f141,f52])).
% 1.33/0.55  fof(f141,plain,(
% 1.33/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f140,f53])).
% 1.33/0.55  fof(f140,plain,(
% 1.33/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f137,f54])).
% 1.33/0.55  fof(f137,plain,(
% 1.33/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 1.33/0.55    inference(resolution,[],[f72,f55])).
% 1.33/0.55  fof(f72,plain,(
% 1.33/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f31])).
% 1.33/0.55  fof(f31,plain,(
% 1.33/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.33/0.55    inference(flattening,[],[f30])).
% 1.33/0.55  fof(f30,plain,(
% 1.33/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.33/0.55    inference(ennf_transformation,[],[f14])).
% 1.33/0.55  fof(f14,axiom,(
% 1.33/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.33/0.55  fof(f61,plain,(
% 1.33/0.55    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f103,plain,(
% 1.33/0.55    v5_relat_1(sK1,sK0)),
% 1.33/0.55    inference(resolution,[],[f75,f55])).
% 1.33/0.55  fof(f75,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f34])).
% 1.33/0.55  fof(f34,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.55    inference(ennf_transformation,[],[f21])).
% 1.33/0.55  fof(f21,plain,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.33/0.55    inference(pure_predicate_removal,[],[f6])).
% 1.33/0.55  fof(f6,axiom,(
% 1.33/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.33/0.55  fof(f297,plain,(
% 1.33/0.55    k1_xboole_0 = sK1 | ~v5_relat_1(sK1,k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f294,f97])).
% 1.33/0.55  fof(f294,plain,(
% 1.33/0.55    k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | ~v5_relat_1(sK1,k1_xboole_0)),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f291])).
% 1.33/0.55  fof(f291,plain,(
% 1.33/0.55    k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | k1_xboole_0 != k1_xboole_0 | ~v5_relat_1(sK1,k1_xboole_0)),
% 1.33/0.55    inference(resolution,[],[f116,f224])).
% 1.33/0.55  fof(f224,plain,(
% 1.33/0.55    v2_funct_2(sK1,k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f131,f212])).
% 1.33/0.55  fof(f116,plain,(
% 1.33/0.55    ( ! [X4,X3] : (~v2_funct_2(X3,X4) | k1_xboole_0 = X3 | ~v1_relat_1(X3) | k1_xboole_0 != X4 | ~v5_relat_1(X3,X4)) )),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f115])).
% 1.33/0.55  fof(f115,plain,(
% 1.33/0.55    ( ! [X4,X3] : (k1_xboole_0 != X4 | k1_xboole_0 = X3 | ~v1_relat_1(X3) | ~v2_funct_2(X3,X4) | ~v5_relat_1(X3,X4) | ~v1_relat_1(X3)) )),
% 1.33/0.55    inference(superposition,[],[f68,f70])).
% 1.33/0.55  fof(f68,plain,(
% 1.33/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f25])).
% 1.33/0.55  fof(f25,plain,(
% 1.33/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(flattening,[],[f24])).
% 1.33/0.55  % (1440)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.33/0.55  fof(f24,plain,(
% 1.33/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(ennf_transformation,[],[f2])).
% 1.33/0.55  fof(f2,axiom,(
% 1.33/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.33/0.55  fof(f52,plain,(
% 1.33/0.55    v1_funct_1(sK1)),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f383,plain,(
% 1.33/0.55    k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f382,f301])).
% 1.33/0.55  fof(f301,plain,(
% 1.33/0.55    v2_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f124,f298])).
% 1.33/0.55  fof(f124,plain,(
% 1.33/0.55    v2_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f123,f52])).
% 1.33/0.55  fof(f123,plain,(
% 1.33/0.55    ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 1.33/0.55    inference(subsumption_resolution,[],[f120,f54])).
% 1.33/0.55  fof(f120,plain,(
% 1.33/0.55    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1)),
% 1.33/0.55    inference(resolution,[],[f77,f55])).
% 1.33/0.55  fof(f77,plain,(
% 1.33/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f36])).
% 1.33/0.55  fof(f382,plain,(
% 1.33/0.55    k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f381])).
% 1.33/0.55  fof(f381,plain,(
% 1.33/0.55    k1_xboole_0 != k6_relat_1(k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) | ~v2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.33/0.55    inference(superposition,[],[f69,f378])).
% 1.33/0.55  fof(f378,plain,(
% 1.33/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f377,f299])).
% 1.33/0.55  fof(f377,plain,(
% 1.33/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f376,f96])).
% 1.33/0.55  fof(f376,plain,(
% 1.33/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f363])).
% 1.33/0.55  fof(f363,plain,(
% 1.33/0.55    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(superposition,[],[f356,f84])).
% 1.33/0.55  fof(f84,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f44])).
% 1.33/0.55  fof(f44,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.33/0.55    inference(flattening,[],[f43])).
% 1.33/0.55  fof(f43,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.33/0.55    inference(ennf_transformation,[],[f13])).
% 1.33/0.55  fof(f13,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.33/0.55  fof(f356,plain,(
% 1.33/0.55    k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f355,f299])).
% 1.33/0.55  fof(f355,plain,(
% 1.33/0.55    k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f354,f96])).
% 1.33/0.55  fof(f354,plain,(
% 1.33/0.55    k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(duplicate_literal_removal,[],[f351])).
% 1.33/0.55  fof(f351,plain,(
% 1.33/0.55    k1_xboole_0 = k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0)),
% 1.33/0.55    inference(resolution,[],[f319,f335])).
% 1.33/0.55  fof(f335,plain,(
% 1.33/0.55    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f312,f321])).
% 1.33/0.55  fof(f321,plain,(
% 1.33/0.55    k1_xboole_0 = sK2),
% 1.33/0.55    inference(subsumption_resolution,[],[f320,f221])).
% 1.33/0.55  fof(f221,plain,(
% 1.33/0.55    v5_relat_1(sK2,k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f104,f212])).
% 1.33/0.55  fof(f104,plain,(
% 1.33/0.55    v5_relat_1(sK2,sK0)),
% 1.33/0.55    inference(resolution,[],[f75,f59])).
% 1.33/0.55  fof(f320,plain,(
% 1.33/0.55    k1_xboole_0 = sK2 | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f293,f98])).
% 1.33/0.55  fof(f98,plain,(
% 1.33/0.55    v1_relat_1(sK2)),
% 1.33/0.55    inference(resolution,[],[f73,f59])).
% 1.33/0.55  fof(f293,plain,(
% 1.33/0.55    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.33/0.55    inference(trivial_inequality_removal,[],[f292])).
% 1.33/0.55  fof(f292,plain,(
% 1.33/0.55    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | k1_xboole_0 != k1_xboole_0 | ~v5_relat_1(sK2,k1_xboole_0)),
% 1.33/0.55    inference(resolution,[],[f116,f225])).
% 1.33/0.55  fof(f225,plain,(
% 1.33/0.55    v2_funct_2(sK2,k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f133,f212])).
% 1.33/0.55  fof(f133,plain,(
% 1.33/0.55    v2_funct_2(sK2,sK0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f132,f56])).
% 1.33/0.55  fof(f132,plain,(
% 1.33/0.55    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 1.33/0.55    inference(subsumption_resolution,[],[f128,f58])).
% 1.33/0.55  fof(f58,plain,(
% 1.33/0.55    v3_funct_2(sK2,sK0,sK0)),
% 1.33/0.55    inference(cnf_transformation,[],[f49])).
% 1.33/0.55  fof(f128,plain,(
% 1.33/0.55    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 1.33/0.55    inference(resolution,[],[f78,f59])).
% 1.33/0.55  fof(f312,plain,(
% 1.33/0.55    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0)),
% 1.33/0.55    inference(backward_demodulation,[],[f238,f298])).
% 1.33/0.55  fof(f238,plain,(
% 1.33/0.55    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k1_xboole_0)),
% 1.33/0.55    inference(forward_demodulation,[],[f219,f62])).
% 1.33/0.55  fof(f219,plain,(
% 1.33/0.55    r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK2),k6_relat_1(k1_xboole_0))),
% 1.33/0.55    inference(backward_demodulation,[],[f90,f212])).
% 1.33/0.55  fof(f319,plain,(
% 1.33/0.55    ( ! [X45,X43,X44,X42] : (~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42),k1_xboole_0) | k1_xboole_0 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45))) | ~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0))) | ~v1_funct_1(X42) | ~v1_funct_1(X44)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f315,f298])).
% 1.33/0.55  fof(f315,plain,(
% 1.33/0.55    ( ! [X45,X43,X44,X42] : (k1_xboole_0 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42) | ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42),sK1) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45))) | ~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0))) | ~v1_funct_1(X42) | ~v1_funct_1(X44)) )),
% 1.33/0.55    inference(backward_demodulation,[],[f247,f298])).
% 1.33/0.55  fof(f247,plain,(
% 1.33/0.55    ( ! [X45,X43,X44,X42] : (~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42),sK1) | sK1 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45))) | ~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0))) | ~v1_funct_1(X42) | ~v1_funct_1(X44)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f246,f212])).
% 1.33/0.55  fof(f246,plain,(
% 1.33/0.55    ( ! [X45,X43,X44,X42] : (sK1 = k1_partfun1(k1_xboole_0,X45,X43,k1_xboole_0,X44,X42) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45))) | ~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0))) | ~v1_funct_1(X42) | ~v1_funct_1(X44) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f245,f212])).
% 1.33/0.55  fof(f245,plain,(
% 1.33/0.55    ( ! [X45,X43,X44,X42] : (~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X45))) | ~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0))) | ~v1_funct_1(X42) | ~v1_funct_1(X44) | sK1 = k1_partfun1(sK0,X45,X43,sK0,X44,X42) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1)) )),
% 1.33/0.55    inference(forward_demodulation,[],[f234,f212])).
% 1.33/0.55  fof(f234,plain,(
% 1.33/0.55    ( ! [X45,X43,X44,X42] : (~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,k1_xboole_0))) | ~v1_funct_1(X42) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(sK0,X45))) | ~v1_funct_1(X44) | sK1 = k1_partfun1(sK0,X45,X43,sK0,X44,X42) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1)) )),
% 1.33/0.55    inference(backward_demodulation,[],[f164,f212])).
% 1.33/0.55  fof(f164,plain,(
% 1.33/0.55    ( ! [X45,X43,X44,X42] : (~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X43,sK0))) | ~v1_funct_1(X42) | ~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(sK0,X45))) | ~v1_funct_1(X44) | sK1 = k1_partfun1(sK0,X45,X43,sK0,X44,X42) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,X45,X43,sK0,X44,X42),sK1)) )),
% 1.33/0.55    inference(resolution,[],[f86,f134])).
% 1.33/0.55  % (1439)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  fof(f134,plain,(
% 1.33/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X0 | ~r2_relset_1(sK0,sK0,X0,sK1)) )),
% 1.33/0.55    inference(resolution,[],[f82,f55])).
% 1.33/0.55  fof(f82,plain,(
% 1.33/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.55    inference(cnf_transformation,[],[f51])).
% 1.33/0.55  fof(f86,plain,(
% 1.33/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f46])).
% 1.33/0.55  fof(f46,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.33/0.55    inference(flattening,[],[f45])).
% 1.33/0.55  fof(f45,plain,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.33/0.55    inference(ennf_transformation,[],[f11])).
% 1.33/0.55  fof(f11,axiom,(
% 1.33/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.33/0.55  fof(f69,plain,(
% 1.33/0.55    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.33/0.55    inference(cnf_transformation,[],[f27])).
% 1.33/0.55  fof(f27,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.33/0.55    inference(flattening,[],[f26])).
% 1.33/0.55  % (1445)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.55  fof(f26,plain,(
% 1.33/0.55    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.33/0.55    inference(ennf_transformation,[],[f4])).
% 1.33/0.55  fof(f4,axiom,(
% 1.33/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.33/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.33/0.55  fof(f334,plain,(
% 1.33/0.55    ~r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 1.33/0.55    inference(backward_demodulation,[],[f309,f321])).
% 1.33/0.56  fof(f309,plain,(
% 1.33/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(k1_xboole_0))),
% 1.33/0.56    inference(backward_demodulation,[],[f229,f298])).
% 1.33/0.56  fof(f229,plain,(
% 1.33/0.56    ~r2_relset_1(k1_xboole_0,k1_xboole_0,sK2,k2_funct_1(sK1))),
% 1.33/0.56    inference(backward_demodulation,[],[f143,f212])).
% 1.33/0.56  % SZS output end Proof for theBenchmark
% 1.33/0.56  % (1427)------------------------------
% 1.33/0.56  % (1427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (1427)Termination reason: Refutation
% 1.33/0.56  
% 1.33/0.56  % (1427)Memory used [KB]: 1918
% 1.33/0.56  % (1427)Time elapsed: 0.140 s
% 1.33/0.56  % (1427)------------------------------
% 1.33/0.56  % (1427)------------------------------
% 1.33/0.56  % (1417)Success in time 0.2 s
%------------------------------------------------------------------------------
