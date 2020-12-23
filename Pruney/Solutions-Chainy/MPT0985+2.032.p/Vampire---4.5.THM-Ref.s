%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  133 (12577 expanded)
%              Number of leaves         :   13 (2392 expanded)
%              Depth                    :   32
%              Number of atoms          :  352 (58094 expanded)
%              Number of equality atoms :   91 (8173 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1028,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1025,f942])).

fof(f942,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f941,f95])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f941,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f626,f555])).

fof(f555,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f412,f424])).

fof(f424,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f237,f391])).

fof(f391,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f137,f389])).

fof(f389,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f365])).

fof(f365,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f147,f362])).

fof(f362,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f361,f341])).

fof(f341,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f243,f149])).

fof(f149,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f148,f133])).

fof(f133,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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

fof(f148,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f130,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f130,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f58,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f243,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | k1_xboole_0 = k1_relat_1(sK2)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f242,f206])).

fof(f206,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f172,f205])).

fof(f205,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f122,f133])).

fof(f122,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f120,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f59,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f172,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) ),
    inference(forward_demodulation,[],[f171,f141])).

fof(f141,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f138,f133])).

fof(f138,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f121,f137])).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f119,f56])).

fof(f119,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f59,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f171,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(subsumption_resolution,[],[f166,f157])).

fof(f157,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f117,f133])).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f166,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(resolution,[],[f164,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f164,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f118,f133])).

fof(f118,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f56,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f242,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
      | ~ r1_tarski(k1_relat_1(sK2),X1)
      | k1_xboole_0 = k1_relat_1(sK2)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(subsumption_resolution,[],[f239,f164])).

fof(f239,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
      | ~ r1_tarski(k1_relat_1(sK2),X1)
      | k1_xboole_0 = k1_relat_1(sK2)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    inference(resolution,[],[f207,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f207,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f170,f205])).

fof(f170,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) ),
    inference(forward_demodulation,[],[f169,f141])).

fof(f169,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f165,f157])).

fof(f165,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f164,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f361,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f358,f164])).

fof(f358,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f325,f55])).

fof(f55,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f325,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | k1_xboole_0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f241,f149])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | k1_xboole_0 = k1_relat_1(sK2)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    inference(subsumption_resolution,[],[f240,f206])).

fof(f240,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | k1_xboole_0 = k1_relat_1(sK2)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    inference(subsumption_resolution,[],[f238,f164])).

fof(f238,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | k1_xboole_0 = k1_relat_1(sK2)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0) ) ),
    inference(resolution,[],[f207,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f147,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f133,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f137,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f134,f60])).

fof(f60,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f134,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f58,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f237,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f145,f137])).

fof(f145,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f133,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f412,plain,(
    k1_xboole_0 = k2_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f410])).

fof(f410,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f294,f391])).

fof(f294,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2) ),
    inference(superposition,[],[f158,f141])).

fof(f158,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2) ),
    inference(resolution,[],[f157,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f626,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f549,f555])).

fof(f549,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f511,f424])).

fof(f511,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f418,f424])).

fof(f418,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f417,f110])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f417,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f416,f391])).

fof(f416,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f392,f164])).

fof(f392,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f55,f391])).

fof(f1025,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    inference(resolution,[],[f1024,f366])).

fof(f366,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f149,f362])).

fof(f1024,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f1023,f95])).

fof(f1023,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f1019,f425])).

fof(f425,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f56,f424])).

fof(f1019,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f634,f114])).

fof(f114,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 != X0
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f634,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f633,f500])).

fof(f500,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f362,f424])).

fof(f633,plain,(
    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f632,f501])).

fof(f501,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f389,f424])).

fof(f632,plain,(
    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f560,f555])).

fof(f560,plain,(
    v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f444,f555])).

fof(f444,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0))),k2_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0)))) ),
    inference(backward_demodulation,[],[f191,f424])).

fof(f191,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2)))) ),
    inference(subsumption_resolution,[],[f187,f173])).

fof(f173,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f167,f157])).

fof(f167,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f164,f63])).

fof(f187,plain,
    ( ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2)))) ),
    inference(resolution,[],[f174,f85])).

fof(f174,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f168,f157])).

fof(f168,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f164,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:12:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (31371)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (31369)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (31379)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (31367)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (31385)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (31388)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (31377)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (31371)Refutation not found, incomplete strategy% (31371)------------------------------
% 0.22/0.51  % (31371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31387)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (31389)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (31376)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (31375)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (31365)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (31380)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (31373)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (31370)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (31372)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (31390)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (31382)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (31371)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31371)Memory used [KB]: 10746
% 0.22/0.53  % (31371)Time elapsed: 0.094 s
% 0.22/0.53  % (31371)------------------------------
% 0.22/0.53  % (31371)------------------------------
% 0.22/0.53  % (31381)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (31366)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (31384)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (31374)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (31378)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (31383)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (31368)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (31386)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (31366)Refutation not found, incomplete strategy% (31366)------------------------------
% 0.22/0.55  % (31366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31366)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31366)Memory used [KB]: 11001
% 0.22/0.55  % (31366)Time elapsed: 0.122 s
% 0.22/0.55  % (31366)------------------------------
% 0.22/0.55  % (31366)------------------------------
% 0.22/0.55  % (31370)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f1028,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f1025,f942])).
% 0.22/0.57  fof(f942,plain,(
% 0.22/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.57    inference(subsumption_resolution,[],[f941,f95])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.57  fof(f941,plain,(
% 0.22/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.57    inference(forward_demodulation,[],[f626,f555])).
% 0.22/0.57  fof(f555,plain,(
% 0.22/0.57    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.57    inference(forward_demodulation,[],[f412,f424])).
% 0.22/0.57  fof(f424,plain,(
% 0.22/0.57    k1_xboole_0 = sK2),
% 0.22/0.57    inference(global_subsumption,[],[f237,f391])).
% 0.22/0.57  fof(f391,plain,(
% 0.22/0.57    k1_xboole_0 = sK1),
% 0.22/0.57    inference(backward_demodulation,[],[f137,f389])).
% 0.22/0.57  fof(f389,plain,(
% 0.22/0.57    k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f365])).
% 0.22/0.57  fof(f365,plain,(
% 0.22/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.57    inference(backward_demodulation,[],[f147,f362])).
% 0.22/0.57  fof(f362,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.57    inference(subsumption_resolution,[],[f361,f341])).
% 0.22/0.57  fof(f341,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.57    inference(resolution,[],[f243,f149])).
% 0.22/0.57  fof(f149,plain,(
% 0.22/0.57    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.57    inference(subsumption_resolution,[],[f148,f133])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    v1_relat_1(sK2)),
% 0.22/0.57    inference(resolution,[],[f58,f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.57    inference(flattening,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.57    inference(negated_conjecture,[],[f27])).
% 0.22/0.57  fof(f27,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.57  fof(f148,plain,(
% 0.22/0.57    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 0.22/0.57    inference(resolution,[],[f130,f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.57  fof(f130,plain,(
% 0.22/0.57    v4_relat_1(sK2,sK0)),
% 0.22/0.57    inference(resolution,[],[f58,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.57  fof(f243,plain,(
% 0.22/0.57    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | k1_xboole_0 = k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f242,f206])).
% 0.22/0.57  fof(f206,plain,(
% 0.22/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.57    inference(backward_demodulation,[],[f172,f205])).
% 0.22/0.57  fof(f205,plain,(
% 0.22/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(resolution,[],[f122,f133])).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f120,f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    v1_funct_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(resolution,[],[f59,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,axiom,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    v2_funct_1(sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f172,plain,(
% 0.22/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.57    inference(forward_demodulation,[],[f171,f141])).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f138,f133])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.22/0.57    inference(backward_demodulation,[],[f121,f137])).
% 0.22/0.57  fof(f121,plain,(
% 0.22/0.57    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(subsumption_resolution,[],[f119,f56])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(resolution,[],[f59,f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f171,plain,(
% 0.22/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.57    inference(subsumption_resolution,[],[f166,f157])).
% 0.22/0.57  fof(f157,plain,(
% 0.22/0.57    v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(resolution,[],[f117,f133])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(resolution,[],[f56,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.57  fof(f166,plain,(
% 0.22/0.57    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.57    inference(resolution,[],[f164,f86])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,axiom,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.57  fof(f164,plain,(
% 0.22/0.57    v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(resolution,[],[f118,f133])).
% 0.22/0.57  fof(f118,plain,(
% 0.22/0.57    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.57    inference(resolution,[],[f56,f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f242,plain,(
% 0.22/0.57    ( ! [X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~r1_tarski(k1_relat_1(sK2),X1) | k1_xboole_0 = k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f239,f164])).
% 0.22/0.57  fof(f239,plain,(
% 0.22/0.57    ( ! [X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~r1_tarski(k1_relat_1(sK2),X1) | k1_xboole_0 = k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) )),
% 0.22/0.57    inference(resolution,[],[f207,f83])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.57    inference(flattening,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.57    inference(ennf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.22/0.57  fof(f207,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.22/0.57    inference(backward_demodulation,[],[f170,f205])).
% 0.22/0.57  fof(f170,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.57    inference(forward_demodulation,[],[f169,f141])).
% 0.22/0.57  fof(f169,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.57    inference(subsumption_resolution,[],[f165,f157])).
% 0.22/0.57  fof(f165,plain,(
% 0.22/0.57    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.57    inference(resolution,[],[f164,f85])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f47])).
% 0.22/0.57  fof(f361,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.57    inference(subsumption_resolution,[],[f358,f164])).
% 0.22/0.57  fof(f358,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.57    inference(resolution,[],[f325,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f325,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.57    inference(resolution,[],[f241,f149])).
% 0.22/0.57  fof(f241,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f240,f206])).
% 0.22/0.57  fof(f240,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~r1_tarski(k1_relat_1(sK2),X0) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f238,f164])).
% 0.22/0.57  fof(f238,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~r1_tarski(k1_relat_1(sK2),X0) | k1_xboole_0 = k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,X0)) )),
% 0.22/0.57    inference(resolution,[],[f207,f82])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f147,plain,(
% 0.22/0.57    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.57    inference(resolution,[],[f133,f72])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    sK1 = k2_relat_1(sK2)),
% 0.22/0.57    inference(forward_demodulation,[],[f134,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.57    inference(resolution,[],[f58,f75])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.57    inference(ennf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.57  fof(f237,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 0.22/0.57    inference(superposition,[],[f145,f137])).
% 0.22/0.57  fof(f145,plain,(
% 0.22/0.57    k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK2),
% 0.22/0.57    inference(resolution,[],[f133,f74])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.57  fof(f412,plain,(
% 0.22/0.57    k1_xboole_0 = k2_funct_1(sK2)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f410])).
% 0.22/0.57  fof(f410,plain,(
% 0.22/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_funct_1(sK2)),
% 0.22/0.57    inference(backward_demodulation,[],[f294,f391])).
% 0.22/0.57  fof(f294,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2)),
% 0.22/0.57    inference(superposition,[],[f158,f141])).
% 0.22/0.57  fof(f158,plain,(
% 0.22/0.57    k1_xboole_0 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2)),
% 0.22/0.57    inference(resolution,[],[f157,f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f626,plain,(
% 0.22/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.57    inference(backward_demodulation,[],[f549,f555])).
% 0.22/0.57  fof(f549,plain,(
% 0.22/0.57    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.22/0.57    inference(forward_demodulation,[],[f511,f424])).
% 0.22/0.57  fof(f511,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.57    inference(backward_demodulation,[],[f418,f424])).
% 0.22/0.57  fof(f418,plain,(
% 0.22/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.57    inference(forward_demodulation,[],[f417,f110])).
% 0.22/0.57  fof(f110,plain,(
% 0.22/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f66])).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.57  fof(f417,plain,(
% 0.22/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.57    inference(forward_demodulation,[],[f416,f391])).
% 0.22/0.57  fof(f416,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.57    inference(subsumption_resolution,[],[f392,f164])).
% 0.22/0.57  fof(f392,plain,(
% 0.22/0.57    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.57    inference(backward_demodulation,[],[f55,f391])).
% 0.22/0.57  fof(f1025,plain,(
% 0.22/0.57    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.57    inference(resolution,[],[f1024,f366])).
% 0.22/0.57  fof(f366,plain,(
% 0.22/0.57    r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.57    inference(backward_demodulation,[],[f149,f362])).
% 0.22/0.57  fof(f1024,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f1023,f95])).
% 0.22/0.57  fof(f1023,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f1019,f425])).
% 0.22/0.57  fof(f425,plain,(
% 0.22/0.57    v1_funct_1(k1_xboole_0)),
% 0.22/0.57    inference(backward_demodulation,[],[f56,f424])).
% 0.22/0.57  fof(f1019,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.57    inference(resolution,[],[f634,f114])).
% 0.22/0.57  fof(f114,plain,(
% 0.22/0.57    ( ! [X2,X3,X1] : (~v1_funct_2(X3,k1_xboole_0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(X1,X2) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 0.22/0.57    inference(equality_resolution,[],[f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 != X0 | v1_funct_2(X3,X0,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f43])).
% 0.22/0.57  fof(f634,plain,(
% 0.22/0.57    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.57    inference(forward_demodulation,[],[f633,f500])).
% 0.22/0.57  fof(f500,plain,(
% 0.22/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.57    inference(backward_demodulation,[],[f362,f424])).
% 0.22/0.57  fof(f633,plain,(
% 0.22/0.57    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.22/0.57    inference(forward_demodulation,[],[f632,f501])).
% 0.22/0.57  fof(f501,plain,(
% 0.22/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.57    inference(backward_demodulation,[],[f389,f424])).
% 0.22/0.57  fof(f632,plain,(
% 0.22/0.57    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.22/0.57    inference(forward_demodulation,[],[f560,f555])).
% 0.22/0.57  fof(f560,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(k1_xboole_0),k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)))),
% 0.22/0.57    inference(backward_demodulation,[],[f444,f555])).
% 0.22/0.57  fof(f444,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0))),k2_relat_1(k2_funct_1(k2_funct_1(k1_xboole_0))))),
% 0.22/0.57    inference(backward_demodulation,[],[f191,f424])).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2))))),
% 0.22/0.57    inference(subsumption_resolution,[],[f187,f173])).
% 0.22/0.57  fof(f173,plain,(
% 0.22/0.57    v1_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 0.22/0.57    inference(subsumption_resolution,[],[f167,f157])).
% 0.22/0.57  fof(f167,plain,(
% 0.22/0.57    ~v1_relat_1(k2_funct_1(sK2)) | v1_relat_1(k2_funct_1(k2_funct_1(sK2)))),
% 0.22/0.57    inference(resolution,[],[f164,f63])).
% 0.22/0.57  fof(f187,plain,(
% 0.22/0.57    ~v1_relat_1(k2_funct_1(k2_funct_1(sK2))) | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2))))),
% 0.22/0.57    inference(resolution,[],[f174,f85])).
% 0.22/0.57  fof(f174,plain,(
% 0.22/0.57    v1_funct_1(k2_funct_1(k2_funct_1(sK2)))),
% 0.22/0.57    inference(subsumption_resolution,[],[f168,f157])).
% 0.22/0.57  fof(f168,plain,(
% 0.22/0.57    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_1(k2_funct_1(k2_funct_1(sK2)))),
% 0.22/0.57    inference(resolution,[],[f164,f64])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (31370)------------------------------
% 0.22/0.57  % (31370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (31370)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (31370)Memory used [KB]: 6524
% 0.22/0.57  % (31370)Time elapsed: 0.114 s
% 0.22/0.57  % (31370)------------------------------
% 0.22/0.57  % (31370)------------------------------
% 0.22/0.57  % (31364)Success in time 0.211 s
%------------------------------------------------------------------------------
