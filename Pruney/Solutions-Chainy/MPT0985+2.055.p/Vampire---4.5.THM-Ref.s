%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:08 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  175 (5007 expanded)
%              Number of leaves         :   20 (1031 expanded)
%              Depth                    :   33
%              Number of atoms          :  436 (20503 expanded)
%              Number of equality atoms :  107 (3076 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22472)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f1835,plain,(
    $false ),
    inference(global_subsumption,[],[f812,f1677,f1834])).

fof(f1834,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(subsumption_resolution,[],[f1833,f443])).

fof(f443,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f441,f119])).

fof(f119,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f107,f105])).

fof(f105,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f107,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f71,f68])).

fof(f71,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f441,plain,(
    ! [X2] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(resolution,[],[f99,f117])).

fof(f117,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f72,f105])).

fof(f72,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f1833,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f1832,f277])).

fof(f277,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f273,f132])).

fof(f132,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f129,f120])).

fof(f120,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f109,f105])).

fof(f109,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f68])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f129,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f78,f118])).

fof(f118,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f108,f105])).

fof(f108,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f70,f68])).

fof(f70,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f273,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f147,f118])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k1_xboole_0
      | k1_relat_1(k4_relat_1(X0)) != k1_xboole_0 ) ),
    inference(resolution,[],[f80,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1832,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f1831,f1764])).

fof(f1764,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f1742])).

fof(f1742,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f423,f1729])).

fof(f1729,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f404,f1727])).

fof(f1727,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f1683])).

fof(f1683,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f213,f1677])).

fof(f213,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f83,f142])).

fof(f142,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f96,f64])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

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

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_xboole_0
      | k1_relat_1(X0) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f404,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f399,f66])).

fof(f66,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f399,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f97,f64])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f423,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f156,f404])).

fof(f156,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f81,f142])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1831,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1817,f277])).

fof(f1817,plain,
    ( ~ m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f1768,f1764])).

fof(f1768,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f1767,f1729])).

fof(f1767,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f1733,f252])).

fof(f252,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f251,f142])).

fof(f251,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f249,f62])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f249,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f87,f245])).

fof(f245,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f244,f142])).

fof(f244,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f243,f62])).

fof(f243,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f88,f65])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f87,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1733,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f248,f1729])).

fof(f248,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f247,f245])).

fof(f247,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f246,f245])).

fof(f246,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f61,f245])).

fof(f61,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f1677,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(global_subsumption,[],[f248,f252,f527,f1676])).

fof(f1676,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f1675,f252])).

fof(f1675,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f1672,f420])).

fof(f420,plain,(
    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f408,f359])).

fof(f359,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f357,f96])).

fof(f357,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f356,f142])).

fof(f356,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f345,f76])).

fof(f345,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f344,f146])).

fof(f146,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f142,f78])).

fof(f344,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f339,f145])).

fof(f145,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f142,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f339,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))))) ),
    inference(resolution,[],[f85,f252])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f408,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f255,f404])).

fof(f255,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f254,f146])).

fof(f254,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f253,f145])).

fof(f253,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    inference(resolution,[],[f252,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1672,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f1003,f421])).

fof(f421,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f412,f359])).

fof(f412,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f345,f404])).

fof(f1003,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,k1_relat_1(sK2))))
      | ~ v1_funct_2(X5,X6,k1_relat_1(sK2))
      | ~ v1_funct_1(X5)
      | k1_xboole_0 = k1_relat_1(sK2)
      | v1_funct_2(X5,X6,sK0) ) ),
    inference(resolution,[],[f103,f168])).

fof(f168,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f167,f142])).

fof(f167,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f164,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f164,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f98,f64])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

% (22466)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f527,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f520,f168])).

fof(f520,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    inference(forward_demodulation,[],[f515,f145])).

fof(f515,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    inference(resolution,[],[f100,f421])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f812,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(resolution,[],[f795,f168])).

fof(f795,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f794,f538])).

fof(f538,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f536,f443])).

fof(f536,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f521,f330])).

fof(f330,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f329,f121])).

fof(f121,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f110,f105])).

fof(f110,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f68])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f329,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_tarski(k1_relat_1(k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f328,f118])).

fof(f328,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f326,f95])).

fof(f326,plain,(
    ! [X0] :
      ( v4_relat_1(k1_xboole_0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f317,f182])).

fof(f182,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f181,f110])).

fof(f181,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) ),
    inference(subsumption_resolution,[],[f179,f108])).

fof(f179,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k6_partfun1(X0)),X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f165,f95])).

fof(f165,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f98,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f317,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,X6)
      | v4_relat_1(k1_xboole_0,X6)
      | k1_xboole_0 != X5 ) ),
    inference(superposition,[],[f300,f310])).

fof(f310,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_relat_1(k6_partfun1(X0))
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f275,f133])).

fof(f133,plain,(
    ! [X2] : k1_relat_1(k4_relat_1(k6_partfun1(X2))) = X2 ),
    inference(forward_demodulation,[],[f131,f109])).

fof(f131,plain,(
    ! [X2] : k2_relat_1(k6_partfun1(X2)) = k1_relat_1(k4_relat_1(k6_partfun1(X2))) ),
    inference(resolution,[],[f78,f108])).

fof(f275,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_relat_1(k4_relat_1(k6_partfun1(X2)))
      | k1_xboole_0 = k4_relat_1(k6_partfun1(X2)) ) ),
    inference(resolution,[],[f147,f108])).

fof(f300,plain,(
    ! [X6,X5] :
      ( v4_relat_1(k4_relat_1(k6_partfun1(X5)),X6)
      | ~ r1_tarski(X5,X6) ) ),
    inference(forward_demodulation,[],[f295,f133])).

fof(f295,plain,(
    ! [X6,X5] :
      ( v4_relat_1(k4_relat_1(k6_partfun1(X5)),X6)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(k6_partfun1(X5))),X6) ) ),
    inference(resolution,[],[f157,f108])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v4_relat_1(k4_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(X0)),X1) ) ),
    inference(resolution,[],[f94,f76])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f521,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(forward_demodulation,[],[f516,f120])).

fof(f516,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X1)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(resolution,[],[f100,f123])).

fof(f123,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f73,f105])).

fof(f794,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
      | ~ r1_tarski(X1,X2)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f792,f119])).

fof(f792,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ r1_tarski(X1,X2)
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | k1_xboole_0 != X1 ) ),
    inference(resolution,[],[f114,f536])).

fof(f114,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X1,X2)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 != X0
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n024.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:05:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.44  % (22452)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.47  % (22468)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.18/0.48  % (22460)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.18/0.48  % (22469)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.48  % (22461)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.49  % (22453)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.49  % (22464)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.49  % (22471)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.50  % (22451)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.50  % (22454)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.50  % (22449)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.50  % (22448)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.51  % (22463)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.51  % (22450)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.51  % (22463)Refutation not found, incomplete strategy% (22463)------------------------------
% 0.18/0.51  % (22463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (22463)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (22463)Memory used [KB]: 10618
% 0.18/0.51  % (22463)Time elapsed: 0.123 s
% 0.18/0.51  % (22463)------------------------------
% 0.18/0.51  % (22463)------------------------------
% 0.18/0.51  % (22459)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.51  % (22447)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.51  % (22455)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.51  % (22446)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.52  % (22456)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.52  % (22446)Refutation not found, incomplete strategy% (22446)------------------------------
% 0.18/0.52  % (22446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (22446)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (22446)Memory used [KB]: 1791
% 0.18/0.52  % (22446)Time elapsed: 0.128 s
% 0.18/0.52  % (22446)------------------------------
% 0.18/0.52  % (22446)------------------------------
% 0.18/0.52  % (22455)Refutation not found, incomplete strategy% (22455)------------------------------
% 0.18/0.52  % (22455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (22458)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.52  % (22455)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (22455)Memory used [KB]: 10746
% 0.18/0.52  % (22455)Time elapsed: 0.109 s
% 0.18/0.52  % (22455)------------------------------
% 0.18/0.52  % (22455)------------------------------
% 0.18/0.52  % (22456)Refutation not found, incomplete strategy% (22456)------------------------------
% 0.18/0.52  % (22456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (22456)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (22456)Memory used [KB]: 10746
% 0.18/0.52  % (22456)Time elapsed: 0.132 s
% 0.18/0.52  % (22456)------------------------------
% 0.18/0.52  % (22456)------------------------------
% 0.18/0.52  % (22475)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.52  % (22473)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.52  % (22468)Refutation not found, incomplete strategy% (22468)------------------------------
% 0.18/0.52  % (22468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (22468)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.52  
% 0.18/0.52  % (22468)Memory used [KB]: 11129
% 0.18/0.52  % (22468)Time elapsed: 0.132 s
% 0.18/0.52  % (22468)------------------------------
% 0.18/0.52  % (22468)------------------------------
% 0.18/0.52  % (22474)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.53  % (22467)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.53  % (22470)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.18/0.53  % (22452)Refutation found. Thanks to Tanya!
% 0.18/0.53  % SZS status Theorem for theBenchmark
% 0.18/0.53  % SZS output start Proof for theBenchmark
% 0.18/0.53  % (22472)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.18/0.53  fof(f1835,plain,(
% 0.18/0.53    $false),
% 0.18/0.53    inference(global_subsumption,[],[f812,f1677,f1834])).
% 0.18/0.53  fof(f1834,plain,(
% 0.18/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.18/0.53    inference(subsumption_resolution,[],[f1833,f443])).
% 0.18/0.53  fof(f443,plain,(
% 0.18/0.53    ( ! [X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.18/0.53    inference(subsumption_resolution,[],[f441,f119])).
% 0.18/0.53  fof(f119,plain,(
% 0.18/0.53    v1_funct_1(k1_xboole_0)),
% 0.18/0.53    inference(superposition,[],[f107,f105])).
% 0.18/0.53  fof(f105,plain,(
% 0.18/0.53    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.18/0.53    inference(definition_unfolding,[],[f67,f68])).
% 0.18/0.53  fof(f68,plain,(
% 0.18/0.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f23])).
% 0.18/0.53  fof(f23,axiom,(
% 0.18/0.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.18/0.53  fof(f67,plain,(
% 0.18/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.18/0.53    inference(cnf_transformation,[],[f8])).
% 0.18/0.53  fof(f8,axiom,(
% 0.18/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.18/0.53  fof(f107,plain,(
% 0.18/0.53    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.18/0.53    inference(definition_unfolding,[],[f71,f68])).
% 0.18/0.53  fof(f71,plain,(
% 0.18/0.53    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f11])).
% 0.18/0.53  fof(f11,axiom,(
% 0.18/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.18/0.53  fof(f441,plain,(
% 0.18/0.53    ( ! [X2] : (~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.18/0.53    inference(resolution,[],[f99,f117])).
% 0.18/0.53  fof(f117,plain,(
% 0.18/0.53    v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.18/0.53    inference(superposition,[],[f72,f105])).
% 0.18/0.53  fof(f72,plain,(
% 0.18/0.53    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f22])).
% 0.18/0.53  fof(f22,axiom,(
% 0.18/0.53    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.18/0.53  fof(f99,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f56])).
% 0.18/0.53  fof(f56,plain,(
% 0.18/0.53    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.53    inference(flattening,[],[f55])).
% 0.18/0.53  fof(f55,plain,(
% 0.18/0.53    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.53    inference(ennf_transformation,[],[f21])).
% 0.18/0.53  fof(f21,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.18/0.53  fof(f1833,plain,(
% 0.18/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.18/0.53    inference(forward_demodulation,[],[f1832,f277])).
% 0.18/0.53  fof(f277,plain,(
% 0.18/0.53    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.18/0.53    inference(subsumption_resolution,[],[f273,f132])).
% 0.18/0.53  fof(f132,plain,(
% 0.18/0.53    k1_xboole_0 = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.18/0.53    inference(forward_demodulation,[],[f129,f120])).
% 0.18/0.53  fof(f120,plain,(
% 0.18/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.18/0.53    inference(superposition,[],[f109,f105])).
% 0.18/0.53  fof(f109,plain,(
% 0.18/0.53    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.18/0.53    inference(definition_unfolding,[],[f75,f68])).
% 0.18/0.53  fof(f75,plain,(
% 0.18/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f6])).
% 0.18/0.53  fof(f6,axiom,(
% 0.18/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.18/0.53  fof(f129,plain,(
% 0.18/0.53    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.18/0.53    inference(resolution,[],[f78,f118])).
% 0.18/0.53  fof(f118,plain,(
% 0.18/0.53    v1_relat_1(k1_xboole_0)),
% 0.18/0.53    inference(superposition,[],[f108,f105])).
% 0.18/0.53  fof(f108,plain,(
% 0.18/0.53    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.18/0.53    inference(definition_unfolding,[],[f70,f68])).
% 0.18/0.53  fof(f70,plain,(
% 0.18/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f11])).
% 0.18/0.53  fof(f78,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f33])).
% 0.18/0.53  fof(f33,plain,(
% 0.18/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f3])).
% 0.18/0.53  fof(f3,axiom,(
% 0.18/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.18/0.53  fof(f273,plain,(
% 0.18/0.53    k1_xboole_0 = k4_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.18/0.53    inference(resolution,[],[f147,f118])).
% 0.18/0.53  fof(f147,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(X0) = k1_xboole_0 | k1_relat_1(k4_relat_1(X0)) != k1_xboole_0) )),
% 0.18/0.53    inference(resolution,[],[f80,f76])).
% 0.18/0.53  fof(f76,plain,(
% 0.18/0.53    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f31])).
% 0.18/0.53  fof(f31,plain,(
% 0.18/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f2])).
% 0.18/0.53  fof(f2,axiom,(
% 0.18/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.18/0.53  fof(f80,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f35])).
% 0.18/0.53  fof(f35,plain,(
% 0.18/0.53    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(flattening,[],[f34])).
% 0.18/0.53  fof(f34,plain,(
% 0.18/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f4])).
% 0.18/0.53  fof(f4,axiom,(
% 0.18/0.53    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.18/0.53  fof(f1832,plain,(
% 0.18/0.53    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.18/0.53    inference(forward_demodulation,[],[f1831,f1764])).
% 0.18/0.53  fof(f1764,plain,(
% 0.18/0.53    k1_xboole_0 = sK2),
% 0.18/0.53    inference(trivial_inequality_removal,[],[f1742])).
% 0.18/0.53  fof(f1742,plain,(
% 0.18/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 0.18/0.53    inference(backward_demodulation,[],[f423,f1729])).
% 0.18/0.53  fof(f1729,plain,(
% 0.18/0.53    k1_xboole_0 = sK1),
% 0.18/0.53    inference(backward_demodulation,[],[f404,f1727])).
% 0.18/0.53  fof(f1727,plain,(
% 0.18/0.53    k1_xboole_0 = k2_relat_1(sK2)),
% 0.18/0.53    inference(trivial_inequality_removal,[],[f1683])).
% 0.18/0.53  fof(f1683,plain,(
% 0.18/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2)),
% 0.18/0.53    inference(backward_demodulation,[],[f213,f1677])).
% 0.18/0.53  fof(f213,plain,(
% 0.18/0.53    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.18/0.53    inference(resolution,[],[f83,f142])).
% 0.18/0.53  fof(f142,plain,(
% 0.18/0.53    v1_relat_1(sK2)),
% 0.18/0.53    inference(resolution,[],[f96,f64])).
% 0.18/0.53  fof(f64,plain,(
% 0.18/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.53    inference(cnf_transformation,[],[f30])).
% 0.18/0.53  fof(f30,plain,(
% 0.18/0.53    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.18/0.53    inference(flattening,[],[f29])).
% 0.18/0.53  fof(f29,plain,(
% 0.18/0.53    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.18/0.53    inference(ennf_transformation,[],[f27])).
% 0.18/0.53  fof(f27,negated_conjecture,(
% 0.18/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.18/0.53    inference(negated_conjecture,[],[f26])).
% 0.18/0.53  fof(f26,conjecture,(
% 0.18/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.18/0.53  fof(f96,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f52])).
% 0.18/0.53  fof(f52,plain,(
% 0.18/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.53    inference(ennf_transformation,[],[f17])).
% 0.18/0.53  fof(f17,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.53  fof(f83,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) != k1_xboole_0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f36])).
% 0.18/0.53  fof(f36,plain,(
% 0.18/0.53    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f5])).
% 0.18/0.53  fof(f5,axiom,(
% 0.18/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.18/0.53  fof(f404,plain,(
% 0.18/0.53    sK1 = k2_relat_1(sK2)),
% 0.18/0.53    inference(forward_demodulation,[],[f399,f66])).
% 0.18/0.53  fof(f66,plain,(
% 0.18/0.53    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.18/0.53    inference(cnf_transformation,[],[f30])).
% 0.18/0.53  fof(f399,plain,(
% 0.18/0.53    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.18/0.53    inference(resolution,[],[f97,f64])).
% 0.18/0.53  fof(f97,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f53])).
% 0.18/0.53  fof(f53,plain,(
% 0.18/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.53    inference(ennf_transformation,[],[f19])).
% 0.18/0.53  fof(f19,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.53  fof(f423,plain,(
% 0.18/0.53    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 0.18/0.53    inference(superposition,[],[f156,f404])).
% 0.18/0.53  fof(f156,plain,(
% 0.18/0.53    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.18/0.53    inference(resolution,[],[f81,f142])).
% 0.18/0.53  fof(f81,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f35])).
% 0.18/0.53  fof(f1831,plain,(
% 0.18/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.18/0.53    inference(forward_demodulation,[],[f1817,f277])).
% 0.18/0.53  fof(f1817,plain,(
% 0.18/0.53    ~m1_subset_1(k4_relat_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.18/0.53    inference(backward_demodulation,[],[f1768,f1764])).
% 0.18/0.53  fof(f1768,plain,(
% 0.18/0.53    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.18/0.53    inference(forward_demodulation,[],[f1767,f1729])).
% 0.18/0.53  fof(f1767,plain,(
% 0.18/0.53    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.18/0.53    inference(subsumption_resolution,[],[f1733,f252])).
% 0.18/0.53  fof(f252,plain,(
% 0.18/0.53    v1_funct_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(subsumption_resolution,[],[f251,f142])).
% 0.18/0.53  fof(f251,plain,(
% 0.18/0.53    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.18/0.53    inference(subsumption_resolution,[],[f249,f62])).
% 0.18/0.53  fof(f62,plain,(
% 0.18/0.53    v1_funct_1(sK2)),
% 0.18/0.53    inference(cnf_transformation,[],[f30])).
% 0.18/0.53  fof(f249,plain,(
% 0.18/0.53    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.18/0.53    inference(superposition,[],[f87,f245])).
% 0.18/0.53  fof(f245,plain,(
% 0.18/0.53    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.18/0.53    inference(subsumption_resolution,[],[f244,f142])).
% 0.18/0.53  fof(f244,plain,(
% 0.18/0.53    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.18/0.53    inference(subsumption_resolution,[],[f243,f62])).
% 0.18/0.53  fof(f243,plain,(
% 0.18/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.18/0.53    inference(resolution,[],[f88,f65])).
% 0.18/0.53  fof(f65,plain,(
% 0.18/0.53    v2_funct_1(sK2)),
% 0.18/0.53    inference(cnf_transformation,[],[f30])).
% 0.18/0.53  fof(f88,plain,(
% 0.18/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f42])).
% 0.18/0.53  fof(f42,plain,(
% 0.18/0.53    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(flattening,[],[f41])).
% 0.18/0.53  fof(f41,plain,(
% 0.18/0.53    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.53    inference(ennf_transformation,[],[f9])).
% 0.18/0.53  fof(f9,axiom,(
% 0.18/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.18/0.53  fof(f87,plain,(
% 0.18/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f40])).
% 0.18/0.53  fof(f40,plain,(
% 0.18/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(flattening,[],[f39])).
% 0.18/0.53  fof(f39,plain,(
% 0.18/0.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.53    inference(ennf_transformation,[],[f10])).
% 0.18/0.53  fof(f10,axiom,(
% 0.18/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.18/0.53  fof(f1733,plain,(
% 0.18/0.53    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(backward_demodulation,[],[f248,f1729])).
% 0.18/0.53  fof(f248,plain,(
% 0.18/0.53    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.18/0.53    inference(forward_demodulation,[],[f247,f245])).
% 0.18/0.53  fof(f247,plain,(
% 0.18/0.53    ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.18/0.53    inference(forward_demodulation,[],[f246,f245])).
% 0.18/0.53  fof(f246,plain,(
% 0.18/0.53    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.18/0.53    inference(backward_demodulation,[],[f61,f245])).
% 0.18/0.53  fof(f61,plain,(
% 0.18/0.53    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.18/0.53    inference(cnf_transformation,[],[f30])).
% 0.18/0.53  fof(f1677,plain,(
% 0.18/0.53    k1_xboole_0 = k1_relat_1(sK2)),
% 0.18/0.53    inference(global_subsumption,[],[f248,f252,f527,f1676])).
% 0.18/0.53  fof(f1676,plain,(
% 0.18/0.53    k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.18/0.53    inference(subsumption_resolution,[],[f1675,f252])).
% 0.18/0.53  fof(f1675,plain,(
% 0.18/0.53    ~v1_funct_1(k4_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.18/0.53    inference(subsumption_resolution,[],[f1672,f420])).
% 0.18/0.53  fof(f420,plain,(
% 0.18/0.53    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 0.18/0.53    inference(subsumption_resolution,[],[f408,f359])).
% 0.18/0.53  fof(f359,plain,(
% 0.18/0.53    v1_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(resolution,[],[f357,f96])).
% 0.18/0.53  fof(f357,plain,(
% 0.18/0.53    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.18/0.53    inference(subsumption_resolution,[],[f356,f142])).
% 0.18/0.53  fof(f356,plain,(
% 0.18/0.53    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_relat_1(sK2)),
% 0.18/0.53    inference(resolution,[],[f345,f76])).
% 0.18/0.53  fof(f345,plain,(
% 0.18/0.53    ~v1_relat_1(k4_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.18/0.53    inference(forward_demodulation,[],[f344,f146])).
% 0.18/0.53  fof(f146,plain,(
% 0.18/0.53    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(resolution,[],[f142,f78])).
% 0.18/0.53  fof(f344,plain,(
% 0.18/0.53    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(forward_demodulation,[],[f339,f145])).
% 0.18/0.53  fof(f145,plain,(
% 0.18/0.53    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(resolution,[],[f142,f79])).
% 0.18/0.53  fof(f79,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f33])).
% 0.18/0.53  fof(f339,plain,(
% 0.18/0.53    ~v1_relat_1(k4_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))))),
% 0.18/0.53    inference(resolution,[],[f85,f252])).
% 0.18/0.53  fof(f85,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f38])).
% 0.18/0.53  fof(f38,plain,(
% 0.18/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(flattening,[],[f37])).
% 0.18/0.53  fof(f37,plain,(
% 0.18/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.53    inference(ennf_transformation,[],[f24])).
% 0.18/0.53  fof(f24,axiom,(
% 0.18/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.18/0.53  fof(f408,plain,(
% 0.18/0.53    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(backward_demodulation,[],[f255,f404])).
% 0.18/0.53  fof(f255,plain,(
% 0.18/0.53    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(forward_demodulation,[],[f254,f146])).
% 0.18/0.53  fof(f254,plain,(
% 0.18/0.53    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(forward_demodulation,[],[f253,f145])).
% 0.18/0.53  fof(f253,plain,(
% 0.18/0.53    ~v1_relat_1(k4_relat_1(sK2)) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))),
% 0.18/0.53    inference(resolution,[],[f252,f84])).
% 0.18/0.53  fof(f84,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f38])).
% 0.18/0.53  fof(f1672,plain,(
% 0.18/0.53    ~v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.18/0.53    inference(resolution,[],[f1003,f421])).
% 0.18/0.53  fof(f421,plain,(
% 0.18/0.53    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.18/0.53    inference(subsumption_resolution,[],[f412,f359])).
% 0.18/0.53  fof(f412,plain,(
% 0.18/0.53    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.18/0.53    inference(backward_demodulation,[],[f345,f404])).
% 0.18/0.53  fof(f1003,plain,(
% 0.18/0.53    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,k1_relat_1(sK2)))) | ~v1_funct_2(X5,X6,k1_relat_1(sK2)) | ~v1_funct_1(X5) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(X5,X6,sK0)) )),
% 0.18/0.53    inference(resolution,[],[f103,f168])).
% 0.18/0.53  fof(f168,plain,(
% 0.18/0.53    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.18/0.53    inference(subsumption_resolution,[],[f167,f142])).
% 0.18/0.53  fof(f167,plain,(
% 0.18/0.53    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 0.18/0.53    inference(resolution,[],[f164,f95])).
% 0.18/0.53  fof(f95,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f51])).
% 0.18/0.53  fof(f51,plain,(
% 0.18/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.53    inference(ennf_transformation,[],[f1])).
% 0.18/0.53  fof(f1,axiom,(
% 0.18/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.18/0.53  fof(f164,plain,(
% 0.18/0.53    v4_relat_1(sK2,sK0)),
% 0.18/0.53    inference(resolution,[],[f98,f64])).
% 0.18/0.53  fof(f98,plain,(
% 0.18/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f54])).
% 0.18/0.53  fof(f54,plain,(
% 0.18/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.53    inference(ennf_transformation,[],[f28])).
% 0.18/0.53  fof(f28,plain,(
% 0.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.18/0.53    inference(pure_predicate_removal,[],[f18])).
% 0.18/0.53  fof(f18,axiom,(
% 0.18/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.53  fof(f103,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f60])).
% 0.18/0.53  fof(f60,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.18/0.53    inference(flattening,[],[f59])).
% 0.18/0.53  fof(f59,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.18/0.53    inference(ennf_transformation,[],[f25])).
% 0.18/0.53  % (22466)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.53  fof(f25,axiom,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.18/0.53  fof(f527,plain,(
% 0.18/0.53    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.18/0.53    inference(resolution,[],[f520,f168])).
% 0.18/0.53  fof(f520,plain,(
% 0.18/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) )),
% 0.18/0.53    inference(forward_demodulation,[],[f515,f145])).
% 0.18/0.53  fof(f515,plain,(
% 0.18/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),X0) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) )),
% 0.18/0.53    inference(resolution,[],[f100,f421])).
% 0.18/0.53  fof(f100,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f58])).
% 0.18/0.53  fof(f58,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.18/0.53    inference(flattening,[],[f57])).
% 0.18/0.53  fof(f57,plain,(
% 0.18/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.18/0.53    inference(ennf_transformation,[],[f20])).
% 0.18/0.53  fof(f20,axiom,(
% 0.18/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.18/0.53  fof(f812,plain,(
% 0.18/0.53    k1_xboole_0 != k1_relat_1(sK2) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.18/0.53    inference(resolution,[],[f795,f168])).
% 0.18/0.53  fof(f795,plain,(
% 0.18/0.53    ( ! [X2,X1] : (~r1_tarski(X1,X2) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | k1_xboole_0 != X1) )),
% 0.18/0.53    inference(subsumption_resolution,[],[f794,f538])).
% 0.18/0.53  fof(f538,plain,(
% 0.18/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 0.18/0.53    inference(resolution,[],[f536,f443])).
% 0.18/0.53  fof(f536,plain,(
% 0.18/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | k1_xboole_0 != X0) )),
% 0.18/0.53    inference(resolution,[],[f521,f330])).
% 0.18/0.53  fof(f330,plain,(
% 0.18/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 0.18/0.53    inference(forward_demodulation,[],[f329,f121])).
% 0.18/0.53  fof(f121,plain,(
% 0.18/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.18/0.53    inference(superposition,[],[f110,f105])).
% 0.18/0.53  fof(f110,plain,(
% 0.18/0.53    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.18/0.53    inference(definition_unfolding,[],[f74,f68])).
% 0.18/0.53  fof(f74,plain,(
% 0.18/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f6])).
% 0.18/0.53  fof(f329,plain,(
% 0.18/0.53    ( ! [X0] : (k1_xboole_0 != X0 | r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.18/0.53    inference(subsumption_resolution,[],[f328,f118])).
% 0.18/0.53  fof(f328,plain,(
% 0.18/0.53    ( ! [X0] : (k1_xboole_0 != X0 | r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.18/0.53    inference(resolution,[],[f326,f95])).
% 0.18/0.53  fof(f326,plain,(
% 0.18/0.53    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0) | k1_xboole_0 != X0) )),
% 0.18/0.53    inference(resolution,[],[f317,f182])).
% 0.18/0.53  fof(f182,plain,(
% 0.18/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.18/0.53    inference(forward_demodulation,[],[f181,f110])).
% 0.18/0.53  fof(f181,plain,(
% 0.18/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k6_partfun1(X0)),X0)) )),
% 0.18/0.53    inference(subsumption_resolution,[],[f179,f108])).
% 0.18/0.53  fof(f179,plain,(
% 0.18/0.53    ( ! [X0] : (r1_tarski(k1_relat_1(k6_partfun1(X0)),X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 0.18/0.53    inference(resolution,[],[f165,f95])).
% 0.18/0.53  fof(f165,plain,(
% 0.18/0.53    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 0.18/0.53    inference(resolution,[],[f98,f73])).
% 0.18/0.53  fof(f73,plain,(
% 0.18/0.53    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f22])).
% 0.18/0.53  fof(f317,plain,(
% 0.18/0.53    ( ! [X6,X5] : (~r1_tarski(X5,X6) | v4_relat_1(k1_xboole_0,X6) | k1_xboole_0 != X5) )),
% 0.18/0.53    inference(superposition,[],[f300,f310])).
% 0.18/0.53  fof(f310,plain,(
% 0.18/0.53    ( ! [X0] : (k1_xboole_0 = k4_relat_1(k6_partfun1(X0)) | k1_xboole_0 != X0) )),
% 0.18/0.53    inference(superposition,[],[f275,f133])).
% 0.18/0.53  fof(f133,plain,(
% 0.18/0.53    ( ! [X2] : (k1_relat_1(k4_relat_1(k6_partfun1(X2))) = X2) )),
% 0.18/0.53    inference(forward_demodulation,[],[f131,f109])).
% 0.18/0.53  fof(f131,plain,(
% 0.18/0.53    ( ! [X2] : (k2_relat_1(k6_partfun1(X2)) = k1_relat_1(k4_relat_1(k6_partfun1(X2)))) )),
% 0.18/0.53    inference(resolution,[],[f78,f108])).
% 0.18/0.53  fof(f275,plain,(
% 0.18/0.53    ( ! [X2] : (k1_xboole_0 != k1_relat_1(k4_relat_1(k6_partfun1(X2))) | k1_xboole_0 = k4_relat_1(k6_partfun1(X2))) )),
% 0.18/0.53    inference(resolution,[],[f147,f108])).
% 0.18/0.53  fof(f300,plain,(
% 0.18/0.53    ( ! [X6,X5] : (v4_relat_1(k4_relat_1(k6_partfun1(X5)),X6) | ~r1_tarski(X5,X6)) )),
% 0.18/0.53    inference(forward_demodulation,[],[f295,f133])).
% 0.18/0.53  fof(f295,plain,(
% 0.18/0.53    ( ! [X6,X5] : (v4_relat_1(k4_relat_1(k6_partfun1(X5)),X6) | ~r1_tarski(k1_relat_1(k4_relat_1(k6_partfun1(X5))),X6)) )),
% 0.18/0.53    inference(resolution,[],[f157,f108])).
% 0.18/0.53  fof(f157,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | v4_relat_1(k4_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(k4_relat_1(X0)),X1)) )),
% 0.18/0.53    inference(resolution,[],[f94,f76])).
% 0.18/0.53  fof(f94,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f51])).
% 0.18/0.53  fof(f521,plain,(
% 0.18/0.53    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.18/0.53    inference(forward_demodulation,[],[f516,f120])).
% 0.18/0.53  fof(f516,plain,(
% 0.18/0.53    ( ! [X1] : (~r1_tarski(k2_relat_1(k1_xboole_0),X1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.18/0.53    inference(resolution,[],[f100,f123])).
% 0.18/0.53  fof(f123,plain,(
% 0.18/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.18/0.53    inference(superposition,[],[f73,f105])).
% 0.18/0.53  fof(f794,plain,(
% 0.18/0.53    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1) | ~r1_tarski(X1,X2) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | k1_xboole_0 != X1) )),
% 0.18/0.53    inference(subsumption_resolution,[],[f792,f119])).
% 0.18/0.53  fof(f792,plain,(
% 0.18/0.53    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(X1,X2) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | k1_xboole_0 != X1) )),
% 0.18/0.53    inference(resolution,[],[f114,f536])).
% 0.18/0.53  fof(f114,plain,(
% 0.18/0.53    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3) | ~r1_tarski(X1,X2) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 0.18/0.53    inference(equality_resolution,[],[f102])).
% 0.18/0.53  fof(f102,plain,(
% 0.18/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 != X0 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f60])).
% 0.18/0.53  % SZS output end Proof for theBenchmark
% 0.18/0.53  % (22452)------------------------------
% 0.18/0.53  % (22452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (22452)Termination reason: Refutation
% 0.18/0.53  
% 0.18/0.53  % (22452)Memory used [KB]: 7036
% 0.18/0.53  % (22452)Time elapsed: 0.136 s
% 0.18/0.53  % (22452)------------------------------
% 0.18/0.53  % (22452)------------------------------
% 0.18/0.53  % (22462)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.53  % (22465)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.54  % (22457)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.54  % (22445)Success in time 0.196 s
%------------------------------------------------------------------------------
