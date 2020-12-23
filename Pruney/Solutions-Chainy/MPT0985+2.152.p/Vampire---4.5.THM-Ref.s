%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 (7161 expanded)
%              Number of leaves         :   15 (1456 expanded)
%              Depth                    :   29
%              Number of atoms          :  307 (32517 expanded)
%              Number of equality atoms :   87 (5222 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(subsumption_resolution,[],[f410,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f410,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f409,f308])).

fof(f308,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f307,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f307,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f306,f50])).

fof(f50,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f306,plain,(
    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f305,f229])).

fof(f229,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f228,f69])).

fof(f228,plain,(
    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f227,f192])).

fof(f192,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f34,f102,f186,f187])).

fof(f187,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f144,f172])).

fof(f172,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f85,f86])).

fof(f86,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f37,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f85,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f84,f37])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f36,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f15])).

% (24622)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f144,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(resolution,[],[f127,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(forward_demodulation,[],[f126,f103])).

fof(f103,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f93,f94])).

fof(f94,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f90,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f90,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f93,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f82,f92])).

fof(f92,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f88,f39])).

fof(f39,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f82,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f126,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(subsumption_resolution,[],[f125,f101])).

fof(f101,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f78,f94])).

fof(f78,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f125,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(subsumption_resolution,[],[f121,f102])).

fof(f121,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(superposition,[],[f64,f108])).

fof(f108,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f83,f94])).

fof(f83,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f186,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f141,f172])).

fof(f141,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f124,f72])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    inference(forward_demodulation,[],[f123,f103])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f122,f101])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f120,f102])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(superposition,[],[f63,f108])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f79,f94])).

fof(f79,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f227,plain,(
    sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f226,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f226,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f203,f69])).

fof(f203,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f110,f192])).

fof(f110,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f89,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f37,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f305,plain,(
    k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f304,f66])).

fof(f304,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f303,f70])).

fof(f70,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f303,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f217,f229])).

fof(f217,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f159,f192])).

fof(f159,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f153,f49])).

fof(f153,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) ),
    inference(resolution,[],[f144,f68])).

fof(f409,plain,(
    ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f331,f269])).

fof(f269,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f262,f50])).

fof(f262,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f224,f229])).

fof(f224,plain,(
    ! [X0] : v1_funct_2(sK2,k1_relat_1(sK2),X0) ),
    inference(subsumption_resolution,[],[f200,f66])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f98,f192])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f97,f94])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ v1_relat_1(sK2)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(superposition,[],[f63,f92])).

fof(f331,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f268,f308])).

fof(f268,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f259,f229])).

fof(f259,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f221,f229])).

fof(f221,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f220,f70])).

fof(f220,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f219,f192])).

fof(f219,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f193,f102])).

fof(f193,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f34,f192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:18:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.46  % (24620)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.47  % (24620)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (24637)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.47  % (24616)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.47  % (24619)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (24626)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f411,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f410,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.48  fof(f410,plain,(
% 0.20/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    inference(forward_demodulation,[],[f409,f308])).
% 0.20/0.48  fof(f308,plain,(
% 0.20/0.48    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.20/0.48    inference(forward_demodulation,[],[f307,f69])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f307,plain,(
% 0.20/0.48    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_xboole_0)),
% 0.20/0.48    inference(forward_demodulation,[],[f306,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.48  fof(f306,plain,(
% 0.20/0.48    k2_funct_1(k1_xboole_0) = k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))),
% 0.20/0.48    inference(forward_demodulation,[],[f305,f229])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    k1_xboole_0 = sK2),
% 0.20/0.48    inference(forward_demodulation,[],[f228,f69])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.20/0.48    inference(forward_demodulation,[],[f227,f192])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    k1_xboole_0 = sK1),
% 0.20/0.48    inference(global_subsumption,[],[f34,f102,f186,f187])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(superposition,[],[f144,f172])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(superposition,[],[f85,f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    inference(resolution,[],[f37,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f17])).
% 0.20/0.48  fof(f17,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f37])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(resolution,[],[f36,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  % (24622)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.20/0.48    inference(resolution,[],[f127,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f126,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f93,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f90,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f37,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(backward_demodulation,[],[f82,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    sK1 = k2_relat_1(sK2)),
% 0.20/0.48    inference(forward_demodulation,[],[f88,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f37,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f38,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    v2_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f125,f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f78,f94])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f35,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f121,f102])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.20/0.48    inference(superposition,[],[f64,f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f83,f94])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f81,f35])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f38,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 0.20/0.48    inference(superposition,[],[f141,f172])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f124,f72])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f123,f103])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f122,f101])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f120,f102])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.20/0.48    inference(superposition,[],[f63,f108])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f79,f94])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f35,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f226,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.48    inference(forward_demodulation,[],[f203,f69])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.48    inference(backward_demodulation,[],[f110,f192])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.48    inference(resolution,[],[f89,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    inference(resolution,[],[f37,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f305,plain,(
% 0.20/0.48    k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f304,f66])).
% 0.20/0.48  fof(f304,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(forward_demodulation,[],[f303,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f303,plain,(
% 0.20/0.48    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)),k2_funct_1(k1_xboole_0)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(forward_demodulation,[],[f217,f229])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(backward_demodulation,[],[f159,f192])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f153,f49])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2)))),
% 0.20/0.48    inference(resolution,[],[f144,f68])).
% 0.20/0.48  fof(f409,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f331,f269])).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f262,f50])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f224,f229])).
% 0.20/0.48  fof(f224,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f200,f66])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f98,f192])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f97,f94])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f35])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 0.20/0.48    inference(superposition,[],[f63,f92])).
% 0.20/0.48  fof(f331,plain,(
% 0.20/0.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    inference(backward_demodulation,[],[f268,f308])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.20/0.48    inference(forward_demodulation,[],[f259,f229])).
% 0.20/0.48  fof(f259,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    inference(backward_demodulation,[],[f221,f229])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.20/0.48    inference(forward_demodulation,[],[f220,f70])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.20/0.48    inference(forward_demodulation,[],[f219,f192])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f193,f102])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(backward_demodulation,[],[f34,f192])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24620)------------------------------
% 0.20/0.48  % (24620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24620)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24620)Memory used [KB]: 6268
% 0.20/0.48  % (24620)Time elapsed: 0.079 s
% 0.20/0.48  % (24620)------------------------------
% 0.20/0.48  % (24620)------------------------------
% 0.20/0.48  % (24614)Success in time 0.133 s
%------------------------------------------------------------------------------
