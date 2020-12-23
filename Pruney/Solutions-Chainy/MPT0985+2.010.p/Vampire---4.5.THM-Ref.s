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
% DateTime   : Thu Dec  3 13:02:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  130 (16925 expanded)
%              Number of leaves         :   13 (3193 expanded)
%              Depth                    :   31
%              Number of atoms          :  341 (81078 expanded)
%              Number of equality atoms :  104 (12910 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f443,plain,(
    $false ),
    inference(resolution,[],[f426,f405])).

fof(f405,plain,(
    ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f328,f401])).

fof(f401,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f393,f397])).

fof(f397,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f396,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f396,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f386,f75])).

fof(f75,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f386,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f307,f334])).

fof(f334,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f333,f317])).

fof(f317,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f294,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f294,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f50,f292])).

fof(f292,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f217,f219,f288,f289])).

fof(f289,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f206,f280])).

fof(f280,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f107,f108])).

fof(f108,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f50,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f107,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f106,f50])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f49,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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

fof(f206,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f165,f186])).

fof(f186,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f103,f110])).

fof(f110,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f103,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f51,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f165,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(resolution,[],[f138,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f138,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(forward_demodulation,[],[f137,f115])).

fof(f115,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f114,f110])).

fof(f114,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f104,f113])).

fof(f113,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f111,f52])).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f111,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f50,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f104,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f101,f48])).

fof(f101,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f51,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f137,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(subsumption_resolution,[],[f136,f122])).

fof(f122,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f98,f110])).

fof(f98,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f48,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f136,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(subsumption_resolution,[],[f132,f123])).

fof(f123,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f99,f110])).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f132,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1))) ) ),
    inference(superposition,[],[f72,f130])).

fof(f130,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f105,f110])).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f102,f48])).

fof(f102,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f51,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f288,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f205,f280])).

fof(f205,plain,(
    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f162,f186])).

fof(f162,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f135,f96])).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    inference(forward_demodulation,[],[f134,f115])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f133,f122])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f131,f123])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(superposition,[],[f71,f130])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f219,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f189,f110])).

fof(f189,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f99,f186])).

fof(f217,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f216,f186])).

fof(f216,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f187,f186])).

fof(f187,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f47,f186])).

fof(f47,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f333,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f331,f88])).

fof(f331,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f293,f92])).

fof(f92,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f293,plain,(
    v1_funct_2(sK2,sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f49,f292])).

fof(f307,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f197,f292])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k4_relat_1(sK2),sK1,X0) ) ),
    inference(backward_demodulation,[],[f135,f186])).

fof(f393,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f328,f334])).

fof(f328,plain,(
    ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f327,f323])).

fof(f323,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f310,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f310,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f206,f292])).

fof(f327,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f326,f89])).

fof(f326,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f325,f292])).

fof(f325,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f314,f219])).

fof(f314,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f217,f292])).

fof(f426,plain,(
    ! [X0] : v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f415,f80])).

fof(f415,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0) ) ),
    inference(backward_demodulation,[],[f307,f411])).

fof(f411,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f410,f317])).

fof(f410,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f409,f88])).

fof(f409,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f406,f404])).

fof(f404,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f296,f401])).

fof(f296,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f108,f292])).

fof(f406,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f402,f90])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f402,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f293,f401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:42:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (2836)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.51  % (2836)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f443,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(resolution,[],[f426,f405])).
% 0.23/0.51  fof(f405,plain,(
% 0.23/0.51    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.23/0.51    inference(backward_demodulation,[],[f328,f401])).
% 0.23/0.51  fof(f401,plain,(
% 0.23/0.51    k1_xboole_0 = sK0),
% 0.23/0.51    inference(subsumption_resolution,[],[f393,f397])).
% 0.23/0.51  fof(f397,plain,(
% 0.23/0.51    ( ! [X0] : (v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0) | k1_xboole_0 = sK0) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f396,f80])).
% 0.23/0.51  fof(f80,plain,(
% 0.23/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.51  fof(f396,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0) | k1_xboole_0 = sK0) )),
% 0.23/0.51    inference(forward_demodulation,[],[f386,f75])).
% 0.23/0.51  fof(f75,plain,(
% 0.23/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.51    inference(cnf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.23/0.51  fof(f386,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,X0) | k1_xboole_0 = sK0) )),
% 0.23/0.51    inference(superposition,[],[f307,f334])).
% 0.23/0.51  fof(f334,plain,(
% 0.23/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK0),
% 0.23/0.51    inference(subsumption_resolution,[],[f333,f317])).
% 0.23/0.51  fof(f317,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.23/0.51    inference(forward_demodulation,[],[f294,f88])).
% 0.23/0.51  fof(f88,plain,(
% 0.23/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.51    inference(equality_resolution,[],[f60])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.51  fof(f294,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.23/0.51    inference(backward_demodulation,[],[f50,f292])).
% 0.23/0.51  fof(f292,plain,(
% 0.23/0.51    k1_xboole_0 = sK1),
% 0.23/0.51    inference(global_subsumption,[],[f217,f219,f288,f289])).
% 0.23/0.51  fof(f289,plain,(
% 0.23/0.51    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK1),
% 0.23/0.51    inference(superposition,[],[f206,f280])).
% 0.23/0.51  fof(f280,plain,(
% 0.23/0.51    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.23/0.51    inference(superposition,[],[f107,f108])).
% 0.23/0.51  fof(f108,plain,(
% 0.23/0.51    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.23/0.51    inference(resolution,[],[f50,f74])).
% 0.23/0.51  fof(f74,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f42])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.51  fof(f107,plain,(
% 0.23/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.23/0.51    inference(subsumption_resolution,[],[f106,f50])).
% 0.23/0.51  fof(f106,plain,(
% 0.23/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.51    inference(resolution,[],[f49,f70])).
% 0.23/0.51  fof(f70,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f38])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(flattening,[],[f37])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.23/0.51    inference(flattening,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.23/0.51    inference(ennf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,negated_conjecture,(
% 0.23/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.23/0.51    inference(negated_conjecture,[],[f22])).
% 0.23/0.51  fof(f22,conjecture,(
% 0.23/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.23/0.51  fof(f206,plain,(
% 0.23/0.51    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.23/0.51    inference(backward_demodulation,[],[f165,f186])).
% 0.23/0.51  fof(f186,plain,(
% 0.23/0.51    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.23/0.51    inference(resolution,[],[f103,f110])).
% 0.23/0.51  fof(f110,plain,(
% 0.23/0.51    v1_relat_1(sK2)),
% 0.23/0.51    inference(resolution,[],[f50,f64])).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f36])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.51  fof(f103,plain,(
% 0.23/0.51    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.23/0.51    inference(subsumption_resolution,[],[f100,f48])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    v1_funct_1(sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.23/0.51    inference(resolution,[],[f51,f55])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(flattening,[],[f28])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,axiom,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    v2_funct_1(sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f165,plain,(
% 0.23/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.23/0.51    inference(resolution,[],[f138,f96])).
% 0.23/0.51  fof(f96,plain,(
% 0.23/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.51    inference(equality_resolution,[],[f84])).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.51  fof(f138,plain,(
% 0.23/0.51    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.23/0.51    inference(forward_demodulation,[],[f137,f115])).
% 0.23/0.51  fof(f115,plain,(
% 0.23/0.51    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(subsumption_resolution,[],[f114,f110])).
% 0.23/0.51  fof(f114,plain,(
% 0.23/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.23/0.51    inference(backward_demodulation,[],[f104,f113])).
% 0.23/0.51  fof(f113,plain,(
% 0.23/0.51    sK1 = k2_relat_1(sK2)),
% 0.23/0.51    inference(forward_demodulation,[],[f111,f52])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f111,plain,(
% 0.23/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.23/0.51    inference(resolution,[],[f50,f62])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.51  fof(f104,plain,(
% 0.23/0.51    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(subsumption_resolution,[],[f101,f48])).
% 0.23/0.51  fof(f101,plain,(
% 0.23/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f51,f53])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(flattening,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,axiom,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.23/0.51  fof(f137,plain,(
% 0.23/0.51    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f136,f122])).
% 0.23/0.51  fof(f122,plain,(
% 0.23/0.51    v1_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f98,f110])).
% 0.23/0.51  fof(f98,plain,(
% 0.23/0.51    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f48,f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(flattening,[],[f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,axiom,(
% 0.23/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.23/0.51  fof(f136,plain,(
% 0.23/0.51    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f132,f123])).
% 0.23/0.51  fof(f123,plain,(
% 0.23/0.51    v1_funct_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f99,f110])).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f48,f57])).
% 0.23/0.51  fof(f57,plain,(
% 0.23/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f132,plain,(
% 0.23/0.51    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X1)))) )),
% 0.23/0.51    inference(superposition,[],[f72,f130])).
% 0.23/0.51  fof(f130,plain,(
% 0.23/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f105,f110])).
% 0.23/0.51  fof(f105,plain,(
% 0.23/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(subsumption_resolution,[],[f102,f48])).
% 0.23/0.51  fof(f102,plain,(
% 0.23/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f51,f54])).
% 0.23/0.51  fof(f54,plain,(
% 0.23/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f27])).
% 0.23/0.51  fof(f72,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f40])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(flattening,[],[f39])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f21])).
% 0.23/0.51  fof(f21,axiom,(
% 0.23/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.23/0.51  fof(f288,plain,(
% 0.23/0.51    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | k1_xboole_0 = sK1),
% 0.23/0.51    inference(superposition,[],[f205,f280])).
% 0.23/0.51  fof(f205,plain,(
% 0.23/0.51    v1_funct_2(k4_relat_1(sK2),sK1,k1_relat_1(sK2))),
% 0.23/0.51    inference(backward_demodulation,[],[f162,f186])).
% 0.23/0.51  fof(f162,plain,(
% 0.23/0.51    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.23/0.51    inference(resolution,[],[f135,f96])).
% 0.23/0.51  fof(f135,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) )),
% 0.23/0.51    inference(forward_demodulation,[],[f134,f115])).
% 0.23/0.51  fof(f134,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f133,f122])).
% 0.23/0.51  fof(f133,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f131,f123])).
% 0.23/0.51  fof(f131,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.23/0.51    inference(superposition,[],[f71,f130])).
% 0.23/0.51  fof(f71,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f40])).
% 0.23/0.51  fof(f219,plain,(
% 0.23/0.51    v1_funct_1(k4_relat_1(sK2))),
% 0.23/0.51    inference(subsumption_resolution,[],[f189,f110])).
% 0.23/0.51  fof(f189,plain,(
% 0.23/0.51    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.23/0.51    inference(backward_demodulation,[],[f99,f186])).
% 0.23/0.51  fof(f217,plain,(
% 0.23/0.51    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.23/0.51    inference(forward_demodulation,[],[f216,f186])).
% 0.23/0.51  fof(f216,plain,(
% 0.23/0.51    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.51    inference(forward_demodulation,[],[f187,f186])).
% 0.23/0.51  fof(f187,plain,(
% 0.23/0.51    ~v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.51    inference(backward_demodulation,[],[f47,f186])).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f333,plain,(
% 0.23/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 0.23/0.51    inference(forward_demodulation,[],[f331,f88])).
% 0.23/0.51  fof(f331,plain,(
% 0.23/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))),
% 0.23/0.51    inference(resolution,[],[f293,f92])).
% 0.23/0.51  fof(f92,plain,(
% 0.23/0.51    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.23/0.51    inference(equality_resolution,[],[f66])).
% 0.23/0.51  fof(f66,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f38])).
% 0.23/0.51  fof(f293,plain,(
% 0.23/0.51    v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.23/0.51    inference(backward_demodulation,[],[f49,f292])).
% 0.23/0.51  fof(f307,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.23/0.51    inference(backward_demodulation,[],[f197,f292])).
% 0.23/0.51  fof(f197,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k4_relat_1(sK2),sK1,X0)) )),
% 0.23/0.51    inference(backward_demodulation,[],[f135,f186])).
% 0.23/0.51  fof(f393,plain,(
% 0.23/0.51    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | k1_xboole_0 = sK0),
% 0.23/0.51    inference(superposition,[],[f328,f334])).
% 0.23/0.51  fof(f328,plain,(
% 0.23/0.51    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.23/0.51    inference(subsumption_resolution,[],[f327,f323])).
% 0.23/0.51  fof(f323,plain,(
% 0.23/0.51    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.23/0.51    inference(forward_demodulation,[],[f310,f89])).
% 0.23/0.51  fof(f89,plain,(
% 0.23/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.23/0.51    inference(equality_resolution,[],[f59])).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f5])).
% 0.23/0.51  fof(f310,plain,(
% 0.23/0.51    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))),
% 0.23/0.51    inference(backward_demodulation,[],[f206,f292])).
% 0.23/0.51  fof(f327,plain,(
% 0.23/0.51    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.23/0.51    inference(forward_demodulation,[],[f326,f89])).
% 0.23/0.51  fof(f326,plain,(
% 0.23/0.51    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.23/0.51    inference(forward_demodulation,[],[f325,f292])).
% 0.23/0.51  fof(f325,plain,(
% 0.23/0.51    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.23/0.51    inference(subsumption_resolution,[],[f314,f219])).
% 0.23/0.51  fof(f314,plain,(
% 0.23/0.51    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.23/0.51    inference(backward_demodulation,[],[f217,f292])).
% 0.23/0.51  fof(f426,plain,(
% 0.23/0.51    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.23/0.51    inference(subsumption_resolution,[],[f415,f80])).
% 0.23/0.51  fof(f415,plain,(
% 0.23/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k4_relat_1(sK2),k1_xboole_0,X0)) )),
% 0.23/0.51    inference(backward_demodulation,[],[f307,f411])).
% 0.23/0.51  fof(f411,plain,(
% 0.23/0.51    k1_xboole_0 = k1_relat_1(sK2)),
% 0.23/0.51    inference(subsumption_resolution,[],[f410,f317])).
% 0.23/0.51  fof(f410,plain,(
% 0.23/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.23/0.51    inference(forward_demodulation,[],[f409,f88])).
% 0.23/0.51  fof(f409,plain,(
% 0.23/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.23/0.51    inference(forward_demodulation,[],[f406,f404])).
% 0.23/0.51  fof(f404,plain,(
% 0.23/0.51    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 0.23/0.51    inference(backward_demodulation,[],[f296,f401])).
% 0.23/0.51  fof(f296,plain,(
% 0.23/0.51    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.23/0.51    inference(backward_demodulation,[],[f108,f292])).
% 0.23/0.51  fof(f406,plain,(
% 0.23/0.51    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.23/0.51    inference(resolution,[],[f402,f90])).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.23/0.51    inference(equality_resolution,[],[f68])).
% 0.23/0.51  fof(f68,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f38])).
% 0.23/0.51  fof(f402,plain,(
% 0.23/0.51    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.23/0.51    inference(backward_demodulation,[],[f293,f401])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (2836)------------------------------
% 0.23/0.51  % (2836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (2836)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (2836)Memory used [KB]: 6396
% 0.23/0.51  % (2836)Time elapsed: 0.098 s
% 0.23/0.51  % (2836)------------------------------
% 0.23/0.51  % (2836)------------------------------
% 0.23/0.51  % (2830)Success in time 0.14 s
%------------------------------------------------------------------------------
