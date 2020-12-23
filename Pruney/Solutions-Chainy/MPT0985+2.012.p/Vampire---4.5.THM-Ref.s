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
% DateTime   : Thu Dec  3 13:02:00 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  133 (4107 expanded)
%              Number of leaves         :   17 ( 780 expanded)
%              Depth                    :   31
%              Number of atoms          :  323 (19390 expanded)
%              Number of equality atoms :   91 (3042 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1362,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1361,f207])).

fof(f207,plain,(
    ! [X5] : v1_funct_2(k1_xboole_0,k1_xboole_0,X5) ),
    inference(superposition,[],[f98,f192])).

fof(f192,plain,(
    ! [X5] : k1_xboole_0 = sK3(k1_xboole_0,X5) ),
    inference(subsumption_resolution,[],[f188,f130])).

fof(f130,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f89,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f188,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0,X5))
      | k1_xboole_0 = sK3(k1_xboole_0,X5) ) ),
    inference(resolution,[],[f87,f140])).

fof(f140,plain,(
    ! [X0] : r1_tarski(sK3(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f138,f89])).

fof(f138,plain,(
    ! [X1] : m1_subset_1(sK3(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f93,f112])).

fof(f112,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f93,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f98,plain,(
    ! [X0,X1] : v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f24])).

fof(f1361,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1360,f126])).

fof(f126,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f125,f65])).

fof(f65,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k4_relat_1(X0) ) ),
    inference(resolution,[],[f70,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f70,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f1360,plain,(
    ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1359,f1278])).

fof(f1278,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f1277,f111])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1277,plain,(
    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1276,f1242])).

fof(f1242,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1236,f1218])).

fof(f1218,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f425,f1211])).

fof(f1211,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f1209,f400])).

fof(f400,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f100,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1209,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f1202,f61])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f1202,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f107,f62])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f425,plain,(
    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f333,f416])).

fof(f416,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f409,f64])).

fof(f64,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f409,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f101,f62])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f333,plain,(
    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f317,f332])).

fof(f332,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f331,f247])).

fof(f247,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f246,f145])).

fof(f145,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f99,f62])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f246,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f244,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f244,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f79,f63])).

fof(f63,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f331,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f330,f145])).

fof(f330,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f328,f60])).

fof(f328,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f81,f63])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f317,plain,(
    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f263,f316])).

fof(f316,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f315,f247])).

fof(f315,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f314,f145])).

fof(f314,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f312,f60])).

fof(f312,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f80,f63])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f263,plain,(
    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f262,f261])).

fof(f261,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f260,f145])).

fof(f260,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f256,f60])).

fof(f256,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f77,f247])).

fof(f77,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f262,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    inference(resolution,[],[f258,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f258,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f257,f145])).

fof(f257,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f255,f60])).

fof(f255,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f78,f247])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1236,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f1222,f275])).

fof(f275,plain,
    ( ~ r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,sK0))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f259,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f259,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f250,f258])).

fof(f250,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f249,f247])).

fof(f249,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f248,f247])).

fof(f248,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f59,f247])).

fof(f59,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f1222,plain,
    ( r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,sK0))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f430,f1211])).

fof(f430,plain,(
    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f338,f416])).

fof(f338,plain,(
    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f322,f332])).

fof(f322,plain,(
    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f309,f316])).

fof(f309,plain,(
    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))) ),
    inference(resolution,[],[f296,f89])).

fof(f296,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(subsumption_resolution,[],[f291,f261])).

fof(f291,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(resolution,[],[f76,f258])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1276,plain,(
    sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1275,f130])).

fof(f1275,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f1247,f111])).

fof(f1247,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f185,f1242])).

fof(f185,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f87,f131])).

fof(f131,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f89,f62])).

fof(f1359,plain,(
    ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1358,f1242])).

fof(f1358,plain,(
    ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f1357,f66])).

fof(f1357,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f1356,f126])).

fof(f1356,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f1355,f1278])).

fof(f1355,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f1249,f112])).

fof(f1249,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f259,f1242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (32692)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (32693)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (32693)Refutation not found, incomplete strategy% (32693)------------------------------
% 0.20/0.49  % (32693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32693)Memory used [KB]: 10746
% 0.20/0.50  % (32693)Time elapsed: 0.073 s
% 0.20/0.50  % (32693)------------------------------
% 0.20/0.50  % (32693)------------------------------
% 0.20/0.52  % (32709)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (32691)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (32700)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (32707)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (32690)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.55  % (32689)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.56  % (32695)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.56  % (32701)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.56  % (32710)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.56  % (32688)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (32704)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.56  % (32713)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.56  % (32694)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.56  % (32712)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.60/0.57  % (32688)Refutation not found, incomplete strategy% (32688)------------------------------
% 1.60/0.57  % (32688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (32688)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (32688)Memory used [KB]: 10746
% 1.60/0.57  % (32688)Time elapsed: 0.158 s
% 1.60/0.57  % (32688)------------------------------
% 1.60/0.57  % (32688)------------------------------
% 1.60/0.57  % (32699)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.60/0.57  % (32708)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.60/0.57  % (32703)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.60/0.57  % (32696)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.60/0.57  % (32698)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.60/0.57  % (32705)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.60/0.58  % (32711)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.60/0.58  % (32697)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.74/0.58  % (32686)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.74/0.60  % (32702)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.74/0.61  % (32707)Refutation found. Thanks to Tanya!
% 1.74/0.61  % SZS status Theorem for theBenchmark
% 1.74/0.61  % SZS output start Proof for theBenchmark
% 1.74/0.61  fof(f1362,plain,(
% 1.74/0.61    $false),
% 1.74/0.61    inference(subsumption_resolution,[],[f1361,f207])).
% 1.74/0.61  fof(f207,plain,(
% 1.74/0.61    ( ! [X5] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X5)) )),
% 1.74/0.61    inference(superposition,[],[f98,f192])).
% 1.74/0.61  fof(f192,plain,(
% 1.74/0.61    ( ! [X5] : (k1_xboole_0 = sK3(k1_xboole_0,X5)) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f188,f130])).
% 1.74/0.61  fof(f130,plain,(
% 1.74/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.74/0.61    inference(resolution,[],[f89,f66])).
% 1.74/0.61  fof(f66,plain,(
% 1.74/0.61    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f5])).
% 1.74/0.61  fof(f5,axiom,(
% 1.74/0.61    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.74/0.61  fof(f89,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f6])).
% 1.74/0.61  fof(f6,axiom,(
% 1.74/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.74/0.61  fof(f188,plain,(
% 1.74/0.61    ( ! [X5] : (~r1_tarski(k1_xboole_0,sK3(k1_xboole_0,X5)) | k1_xboole_0 = sK3(k1_xboole_0,X5)) )),
% 1.74/0.61    inference(resolution,[],[f87,f140])).
% 1.74/0.61  fof(f140,plain,(
% 1.74/0.61    ( ! [X0] : (r1_tarski(sK3(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.74/0.61    inference(resolution,[],[f138,f89])).
% 1.74/0.61  fof(f138,plain,(
% 1.74/0.61    ( ! [X1] : (m1_subset_1(sK3(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.74/0.61    inference(superposition,[],[f93,f112])).
% 1.74/0.61  fof(f112,plain,(
% 1.74/0.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.74/0.61    inference(equality_resolution,[],[f91])).
% 1.74/0.61  fof(f91,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f4])).
% 1.74/0.61  fof(f4,axiom,(
% 1.74/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.74/0.61  fof(f93,plain,(
% 1.74/0.61    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f24])).
% 1.74/0.61  fof(f24,axiom,(
% 1.74/0.61    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 1.74/0.61  fof(f87,plain,(
% 1.74/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.74/0.61    inference(cnf_transformation,[],[f3])).
% 1.74/0.61  fof(f3,axiom,(
% 1.74/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.74/0.61  fof(f98,plain,(
% 1.74/0.61    ( ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f24])).
% 1.74/0.61  fof(f1361,plain,(
% 1.74/0.61    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 1.74/0.61    inference(forward_demodulation,[],[f1360,f126])).
% 1.74/0.61  fof(f126,plain,(
% 1.74/0.61    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.74/0.61    inference(resolution,[],[f125,f65])).
% 1.74/0.61  fof(f65,plain,(
% 1.74/0.61    v1_xboole_0(k1_xboole_0)),
% 1.74/0.61    inference(cnf_transformation,[],[f1])).
% 1.74/0.61  fof(f1,axiom,(
% 1.74/0.61    v1_xboole_0(k1_xboole_0)),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.74/0.61  fof(f125,plain,(
% 1.74/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k4_relat_1(X0)) )),
% 1.74/0.61    inference(resolution,[],[f70,f69])).
% 1.74/0.61  fof(f69,plain,(
% 1.74/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.74/0.61    inference(cnf_transformation,[],[f32])).
% 1.74/0.61  fof(f32,plain,(
% 1.74/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.74/0.61    inference(ennf_transformation,[],[f2])).
% 1.74/0.61  fof(f2,axiom,(
% 1.74/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.74/0.61  fof(f70,plain,(
% 1.74/0.61    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f33])).
% 1.74/0.61  fof(f33,plain,(
% 1.74/0.61    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 1.74/0.61    inference(ennf_transformation,[],[f9])).
% 1.74/0.61  fof(f9,axiom,(
% 1.74/0.61    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).
% 1.74/0.61  fof(f1360,plain,(
% 1.74/0.61    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)),
% 1.74/0.61    inference(forward_demodulation,[],[f1359,f1278])).
% 1.74/0.61  fof(f1278,plain,(
% 1.74/0.61    k1_xboole_0 = sK2),
% 1.74/0.61    inference(forward_demodulation,[],[f1277,f111])).
% 1.74/0.61  fof(f111,plain,(
% 1.74/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.74/0.61    inference(equality_resolution,[],[f92])).
% 1.74/0.61  fof(f92,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f4])).
% 1.74/0.61  fof(f1277,plain,(
% 1.74/0.61    sK2 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 1.74/0.61    inference(forward_demodulation,[],[f1276,f1242])).
% 1.74/0.61  fof(f1242,plain,(
% 1.74/0.61    k1_xboole_0 = sK1),
% 1.74/0.61    inference(subsumption_resolution,[],[f1236,f1218])).
% 1.74/0.61  fof(f1218,plain,(
% 1.74/0.61    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 1.74/0.61    inference(superposition,[],[f425,f1211])).
% 1.74/0.61  fof(f1211,plain,(
% 1.74/0.61    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.74/0.61    inference(superposition,[],[f1209,f400])).
% 1.74/0.61  fof(f400,plain,(
% 1.74/0.61    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.74/0.61    inference(resolution,[],[f100,f62])).
% 1.74/0.61  fof(f62,plain,(
% 1.74/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.74/0.61    inference(cnf_transformation,[],[f29])).
% 1.74/0.61  fof(f29,plain,(
% 1.74/0.61    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.74/0.61    inference(flattening,[],[f28])).
% 1.74/0.61  fof(f28,plain,(
% 1.74/0.61    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.74/0.61    inference(ennf_transformation,[],[f27])).
% 1.74/0.61  fof(f27,negated_conjecture,(
% 1.74/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.74/0.61    inference(negated_conjecture,[],[f26])).
% 1.74/0.61  fof(f26,conjecture,(
% 1.74/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.74/0.61  fof(f100,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f53])).
% 1.74/0.61  fof(f53,plain,(
% 1.74/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.61    inference(ennf_transformation,[],[f21])).
% 1.74/0.61  fof(f21,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.74/0.61  fof(f1209,plain,(
% 1.74/0.61    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.74/0.61    inference(subsumption_resolution,[],[f1202,f61])).
% 1.74/0.61  fof(f61,plain,(
% 1.74/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.74/0.61    inference(cnf_transformation,[],[f29])).
% 1.74/0.61  fof(f1202,plain,(
% 1.74/0.61    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.74/0.61    inference(resolution,[],[f107,f62])).
% 1.74/0.61  fof(f107,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f56])).
% 1.74/0.61  fof(f56,plain,(
% 1.74/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.61    inference(flattening,[],[f55])).
% 1.74/0.61  fof(f55,plain,(
% 1.74/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.61    inference(ennf_transformation,[],[f23])).
% 1.74/0.61  fof(f23,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.74/0.61  fof(f425,plain,(
% 1.74/0.61    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 1.74/0.61    inference(backward_demodulation,[],[f333,f416])).
% 1.74/0.61  fof(f416,plain,(
% 1.74/0.61    sK1 = k2_relat_1(sK2)),
% 1.74/0.61    inference(forward_demodulation,[],[f409,f64])).
% 1.74/0.61  fof(f64,plain,(
% 1.74/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.74/0.61    inference(cnf_transformation,[],[f29])).
% 1.74/0.61  fof(f409,plain,(
% 1.74/0.61    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.74/0.61    inference(resolution,[],[f101,f62])).
% 1.74/0.61  fof(f101,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f54])).
% 1.74/0.61  fof(f54,plain,(
% 1.74/0.61    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.61    inference(ennf_transformation,[],[f22])).
% 1.74/0.61  fof(f22,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.74/0.61  fof(f333,plain,(
% 1.74/0.61    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.74/0.61    inference(backward_demodulation,[],[f317,f332])).
% 1.74/0.61  fof(f332,plain,(
% 1.74/0.61    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 1.74/0.61    inference(forward_demodulation,[],[f331,f247])).
% 1.74/0.61  fof(f247,plain,(
% 1.74/0.61    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f246,f145])).
% 1.74/0.61  fof(f145,plain,(
% 1.74/0.61    v1_relat_1(sK2)),
% 1.74/0.61    inference(resolution,[],[f99,f62])).
% 1.74/0.61  fof(f99,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f52])).
% 1.74/0.61  fof(f52,plain,(
% 1.74/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.61    inference(ennf_transformation,[],[f20])).
% 1.74/0.61  fof(f20,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.74/0.61  fof(f246,plain,(
% 1.74/0.61    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f244,f60])).
% 1.74/0.61  fof(f60,plain,(
% 1.74/0.61    v1_funct_1(sK2)),
% 1.74/0.61    inference(cnf_transformation,[],[f29])).
% 1.74/0.61  fof(f244,plain,(
% 1.74/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.74/0.61    inference(resolution,[],[f79,f63])).
% 1.74/0.61  fof(f63,plain,(
% 1.74/0.61    v2_funct_1(sK2)),
% 1.74/0.61    inference(cnf_transformation,[],[f29])).
% 1.74/0.61  fof(f79,plain,(
% 1.74/0.61    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f43])).
% 1.74/0.61  fof(f43,plain,(
% 1.74/0.61    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.61    inference(flattening,[],[f42])).
% 1.74/0.61  fof(f42,plain,(
% 1.74/0.61    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f14])).
% 1.74/0.61  fof(f14,axiom,(
% 1.74/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.74/0.61  fof(f331,plain,(
% 1.74/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    inference(subsumption_resolution,[],[f330,f145])).
% 1.74/0.61  fof(f330,plain,(
% 1.74/0.61    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    inference(subsumption_resolution,[],[f328,f60])).
% 1.74/0.61  fof(f328,plain,(
% 1.74/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    inference(resolution,[],[f81,f63])).
% 1.74/0.61  fof(f81,plain,(
% 1.74/0.61    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f45])).
% 1.74/0.61  fof(f45,plain,(
% 1.74/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.61    inference(flattening,[],[f44])).
% 1.74/0.61  fof(f44,plain,(
% 1.74/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f19])).
% 1.74/0.61  fof(f19,axiom,(
% 1.74/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.74/0.61  fof(f317,plain,(
% 1.74/0.61    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2)))),
% 1.74/0.61    inference(backward_demodulation,[],[f263,f316])).
% 1.74/0.61  fof(f316,plain,(
% 1.74/0.61    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 1.74/0.61    inference(forward_demodulation,[],[f315,f247])).
% 1.74/0.61  fof(f315,plain,(
% 1.74/0.61    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    inference(subsumption_resolution,[],[f314,f145])).
% 1.74/0.61  fof(f314,plain,(
% 1.74/0.61    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    inference(subsumption_resolution,[],[f312,f60])).
% 1.74/0.61  fof(f312,plain,(
% 1.74/0.61    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.74/0.61    inference(resolution,[],[f80,f63])).
% 1.74/0.61  fof(f80,plain,(
% 1.74/0.61    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f45])).
% 1.74/0.61  fof(f263,plain,(
% 1.74/0.61    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))),
% 1.74/0.61    inference(subsumption_resolution,[],[f262,f261])).
% 1.74/0.61  fof(f261,plain,(
% 1.74/0.61    v1_relat_1(k4_relat_1(sK2))),
% 1.74/0.61    inference(subsumption_resolution,[],[f260,f145])).
% 1.74/0.61  fof(f260,plain,(
% 1.74/0.61    v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f256,f60])).
% 1.74/0.61  fof(f256,plain,(
% 1.74/0.61    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(superposition,[],[f77,f247])).
% 1.74/0.61  fof(f77,plain,(
% 1.74/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f41])).
% 1.74/0.61  fof(f41,plain,(
% 1.74/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.61    inference(flattening,[],[f40])).
% 1.74/0.61  fof(f40,plain,(
% 1.74/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f15])).
% 1.74/0.61  fof(f15,axiom,(
% 1.74/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.74/0.61  fof(f262,plain,(
% 1.74/0.61    ~v1_relat_1(k4_relat_1(sK2)) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))),
% 1.74/0.61    inference(resolution,[],[f258,f75])).
% 1.74/0.61  fof(f75,plain,(
% 1.74/0.61    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f39])).
% 1.74/0.61  fof(f39,plain,(
% 1.74/0.61    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.61    inference(flattening,[],[f38])).
% 1.74/0.61  fof(f38,plain,(
% 1.74/0.61    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f25])).
% 1.74/0.61  fof(f25,axiom,(
% 1.74/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.74/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.74/0.61  fof(f258,plain,(
% 1.74/0.61    v1_funct_1(k4_relat_1(sK2))),
% 1.74/0.61    inference(subsumption_resolution,[],[f257,f145])).
% 1.74/0.61  fof(f257,plain,(
% 1.74/0.61    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f255,f60])).
% 1.74/0.61  fof(f255,plain,(
% 1.74/0.61    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(superposition,[],[f78,f247])).
% 1.74/0.61  fof(f78,plain,(
% 1.74/0.61    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f41])).
% 1.74/0.61  fof(f1236,plain,(
% 1.74/0.61    k1_xboole_0 = sK1 | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(resolution,[],[f1222,f275])).
% 1.74/0.61  fof(f275,plain,(
% 1.74/0.61    ~r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,sK0)) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(resolution,[],[f259,f88])).
% 1.74/0.61  fof(f88,plain,(
% 1.74/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f6])).
% 1.74/0.61  fof(f259,plain,(
% 1.74/0.61    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f250,f258])).
% 1.74/0.61  fof(f250,plain,(
% 1.74/0.61    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.74/0.61    inference(forward_demodulation,[],[f249,f247])).
% 1.74/0.61  fof(f249,plain,(
% 1.74/0.61    ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(forward_demodulation,[],[f248,f247])).
% 1.74/0.61  fof(f248,plain,(
% 1.74/0.61    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(backward_demodulation,[],[f59,f247])).
% 1.74/0.61  fof(f59,plain,(
% 1.74/0.61    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.74/0.61    inference(cnf_transformation,[],[f29])).
% 1.74/0.61  fof(f1222,plain,(
% 1.74/0.61    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,sK0)) | k1_xboole_0 = sK1),
% 1.74/0.61    inference(superposition,[],[f430,f1211])).
% 1.74/0.61  fof(f430,plain,(
% 1.74/0.61    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2)))),
% 1.74/0.61    inference(backward_demodulation,[],[f338,f416])).
% 1.74/0.61  fof(f338,plain,(
% 1.74/0.61    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))),
% 1.74/0.61    inference(backward_demodulation,[],[f322,f332])).
% 1.74/0.61  fof(f322,plain,(
% 1.74/0.61    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))))),
% 1.74/0.61    inference(backward_demodulation,[],[f309,f316])).
% 1.74/0.61  fof(f309,plain,(
% 1.74/0.61    r1_tarski(k4_relat_1(sK2),k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))),
% 1.74/0.61    inference(resolution,[],[f296,f89])).
% 1.74/0.61  fof(f296,plain,(
% 1.74/0.61    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 1.74/0.61    inference(subsumption_resolution,[],[f291,f261])).
% 1.74/0.61  fof(f291,plain,(
% 1.74/0.61    ~v1_relat_1(k4_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 1.74/0.61    inference(resolution,[],[f76,f258])).
% 1.74/0.61  fof(f76,plain,(
% 1.74/0.61    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f39])).
% 1.74/0.61  fof(f1276,plain,(
% 1.74/0.61    sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.74/0.61    inference(subsumption_resolution,[],[f1275,f130])).
% 1.74/0.61  fof(f1275,plain,(
% 1.74/0.61    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.74/0.61    inference(forward_demodulation,[],[f1247,f111])).
% 1.74/0.61  fof(f1247,plain,(
% 1.74/0.61    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.74/0.61    inference(backward_demodulation,[],[f185,f1242])).
% 1.74/0.61  fof(f185,plain,(
% 1.74/0.61    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.74/0.61    inference(resolution,[],[f87,f131])).
% 1.74/0.61  fof(f131,plain,(
% 1.74/0.61    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.74/0.61    inference(resolution,[],[f89,f62])).
% 1.74/0.61  fof(f1359,plain,(
% 1.74/0.61    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 1.74/0.61    inference(forward_demodulation,[],[f1358,f1242])).
% 1.74/0.61  fof(f1358,plain,(
% 1.74/0.61    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(subsumption_resolution,[],[f1357,f66])).
% 1.74/0.61  fof(f1357,plain,(
% 1.74/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(forward_demodulation,[],[f1356,f126])).
% 1.74/0.61  fof(f1356,plain,(
% 1.74/0.61    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(forward_demodulation,[],[f1355,f1278])).
% 1.74/0.61  fof(f1355,plain,(
% 1.74/0.61    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(forward_demodulation,[],[f1249,f112])).
% 1.74/0.61  fof(f1249,plain,(
% 1.74/0.61    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 1.74/0.61    inference(backward_demodulation,[],[f259,f1242])).
% 1.74/0.61  % SZS output end Proof for theBenchmark
% 1.74/0.61  % (32707)------------------------------
% 1.74/0.61  % (32707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (32707)Termination reason: Refutation
% 1.74/0.61  
% 1.74/0.61  % (32707)Memory used [KB]: 2174
% 1.74/0.61  % (32707)Time elapsed: 0.144 s
% 1.74/0.61  % (32707)------------------------------
% 1.74/0.61  % (32707)------------------------------
% 1.74/0.61  % (32685)Success in time 0.25 s
%------------------------------------------------------------------------------
