%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 (5767 expanded)
%              Number of leaves         :   12 (1161 expanded)
%              Depth                    :   29
%              Number of atoms          :  269 (25481 expanded)
%              Number of equality atoms :   98 (4319 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f244,f220])).

fof(f220,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f193,f210])).

fof(f210,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f85,f209])).

fof(f209,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f207])).

fof(f207,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f125,f204])).

fof(f204,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f188,f203])).

fof(f203,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f196,f184])).

fof(f184,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f32,f182])).

fof(f182,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f181,f166])).

fof(f166,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f165,f32])).

fof(f165,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f47,f70])).

fof(f70,plain,(
    k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f181,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f164,f179])).

fof(f179,plain,(
    sK1 = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f176,f85])).

fof(f176,plain,(
    k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(resolution,[],[f166,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f164,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f163,f143])).

fof(f143,plain,(
    v1_funct_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f142,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f142,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f141,f75])).

fof(f75,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f73,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f73,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f141,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f41,f110])).

fof(f110,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f63,f75])).

fof(f63,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f62,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f33,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f163,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(resolution,[],[f120,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f120,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f119,f110])).

fof(f119,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f112,f110])).

fof(f112,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f29,f110])).

fof(f29,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f196,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    inference(resolution,[],[f183,f54])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f183,plain,(
    v1_funct_2(sK2,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f31,f182])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f188,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2) ),
    inference(backward_demodulation,[],[f72,f182])).

fof(f72,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f32,f44])).

fof(f125,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))
    | k1_xboole_0 != k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f124,f110])).

fof(f124,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f117,f78])).

fof(f78,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f75,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f117,plain,
    ( k1_xboole_0 != k2_relat_1(k4_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f90,f110])).

fof(f90,plain,
    ( k1_xboole_0 != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_xboole_0
      | k1_relat_1(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f76,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f77,f74])).

fof(f74,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f71,f34])).

fof(f34,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f77,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f75,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f193,plain,(
    sK1 = k1_relset_1(sK1,k1_xboole_0,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f179,f182])).

fof(f244,plain,(
    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f237,f218])).

fof(f218,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f190,f210])).

fof(f190,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f166,f182])).

fof(f237,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k4_relat_1(sK2)) ),
    inference(resolution,[],[f225,f55])).

fof(f55,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f225,plain,(
    ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f224,f218])).

fof(f224,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f221,f210])).

fof(f221,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f195,f210])).

fof(f195,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f194,f182])).

fof(f194,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f189,f143])).

fof(f189,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0)
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f120,f182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (4863)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (4856)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (4861)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (4869)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (4869)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (4860)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f244,f220])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k4_relat_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f193,f210])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    k1_xboole_0 = sK1),
% 0.20/0.50    inference(backward_demodulation,[],[f85,f209])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f207])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f125,f204])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f188,f203])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f196,f184])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.20/0.50    inference(backward_demodulation,[],[f32,f182])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    k1_xboole_0 = sK0),
% 0.20/0.50    inference(subsumption_resolution,[],[f181,f166])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f165,f32])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(superposition,[],[f47,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f32,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    sK1 != sK1 | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0),
% 0.20/0.50    inference(backward_demodulation,[],[f164,f179])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    sK1 = k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f176,f85])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f166,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f163,f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    v1_funct_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f142,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f141,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f73,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f32,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2)),
% 0.20/0.50    inference(superposition,[],[f41,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f63,f75])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f62,f30])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f33,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f162])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f120,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f119,f110])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    inference(forward_demodulation,[],[f112,f110])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ~v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    inference(backward_demodulation,[],[f29,f110])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f183,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_xboole_0,sK1)),
% 0.20/0.50    inference(backward_demodulation,[],[f31,f182])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,sK1,sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f72,f182])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f32,f44])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k4_relat_1(sK2)) | k1_xboole_0 != k1_relat_1(sK2)),
% 0.20/0.50    inference(forward_demodulation,[],[f124,f110])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f117,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f75,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(k4_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f90,f110])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    k1_xboole_0 != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f76,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f75,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f30,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f77,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    sK1 = k2_relat_1(sK2)),
% 0.20/0.50    inference(forward_demodulation,[],[f71,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.20/0.50    inference(resolution,[],[f32,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f75,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    sK1 = k1_relset_1(sK1,k1_xboole_0,k4_relat_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f179,f182])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k4_relat_1(sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f237,f218])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.50    inference(backward_demodulation,[],[f190,f210])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.20/0.50    inference(backward_demodulation,[],[f166,f182])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k4_relat_1(sK2))),
% 0.20/0.50    inference(resolution,[],[f225,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f224,f218])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(forward_demodulation,[],[f221,f210])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.20/0.50    inference(backward_demodulation,[],[f195,f210])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0)),
% 0.20/0.50    inference(forward_demodulation,[],[f194,f182])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f189,f143])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),sK1,k1_xboole_0) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2))),
% 0.20/0.50    inference(backward_demodulation,[],[f120,f182])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (4869)------------------------------
% 0.20/0.50  % (4869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4869)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (4869)Memory used [KB]: 1663
% 0.20/0.50  % (4869)Time elapsed: 0.087 s
% 0.20/0.50  % (4869)------------------------------
% 0.20/0.50  % (4869)------------------------------
% 0.20/0.50  % (4870)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (4855)Success in time 0.139 s
%------------------------------------------------------------------------------
