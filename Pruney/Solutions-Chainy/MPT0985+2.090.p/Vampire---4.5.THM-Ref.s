%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 (4225 expanded)
%              Number of leaves         :   14 (1063 expanded)
%              Depth                    :   21
%              Number of atoms          :  262 (24985 expanded)
%              Number of equality atoms :   83 (3896 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(subsumption_resolution,[],[f287,f197])).

fof(f197,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f183,f192])).

fof(f192,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f168,f43])).

fof(f43,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f168,plain,(
    k2_relat_1(k1_xboole_0) = sK1 ),
    inference(backward_demodulation,[],[f88,f164])).

fof(f164,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f154,f97])).

fof(f97,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f69,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f154,plain,(
    sK2 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f104,f144])).

fof(f144,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f143,f115])).

fof(f115,plain,(
    ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f96,f102,f41])).

fof(f41,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f85,f94])).

fof(f94,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f39,f36,f69,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f39,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f72,f71])).

fof(f71,plain,(
    k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f72,plain,(
    m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f96,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f36,f69,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f143,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f131,f101])).

fof(f101,plain,(
    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f86,f94])).

fof(f86,plain,(
    sK1 = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f84,f71])).

fof(f84,plain,(
    sK1 = k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f74,f40])).

fof(f40,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

fof(f131,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | k1_xboole_0 = sK0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f102,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f104,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f69,f73,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f73,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f88,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f70,f40])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f183,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f145,f164])).

fof(f145,plain,(
    v1_funct_2(sK2,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f37,f144])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f287,plain,(
    ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f206,f271])).

fof(f271,plain,(
    k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f270,f174])).

fof(f174,plain,(
    k1_xboole_0 = k7_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f105,f164])).

fof(f105,plain,(
    k1_xboole_0 = k7_relat_1(k2_funct_1(sK2),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f95,f44])).

fof(f95,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f36,f69,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f270,plain,(
    k2_funct_1(k1_xboole_0) = k7_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f170,f196,f48])).

fof(f196,plain,(
    v4_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f182,f192])).

fof(f182,plain,(
    v4_relat_1(k2_funct_1(k1_xboole_0),sK1) ),
    inference(backward_demodulation,[],[f120,f164])).

fof(f120,plain,(
    v4_relat_1(k2_funct_1(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f102,f53])).

fof(f170,plain,(
    v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f95,f164])).

fof(f206,plain,(
    ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f205,f164])).

fof(f205,plain,(
    ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f204,f192])).

fof(f204,plain,(
    ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f203,f201])).

fof(f201,plain,(
    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f189,f192])).

fof(f189,plain,(
    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f152,f164])).

fof(f152,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f102,f144])).

fof(f203,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f191,f192])).

fof(f191,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f163,f164])).

fof(f163,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f162,f144])).

fof(f162,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f148,f96])).

fof(f148,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f41,f144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (19187)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (19186)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (19198)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (19189)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (19192)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (19198)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f287,f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f183,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    k1_xboole_0 = sK1),
% 0.21/0.49    inference(forward_demodulation,[],[f168,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    k2_relat_1(k1_xboole_0) = sK1),
% 0.21/0.49    inference(backward_demodulation,[],[f88,f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    k1_xboole_0 = sK2),
% 0.21/0.49    inference(forward_demodulation,[],[f154,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f69,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f38,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    sK2 = k7_relat_1(sK2,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f104,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f143,f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f96,f102,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f85,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f39,f36,f69,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(X0) = k4_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f72,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    k4_relat_1(sK2) = k3_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f38,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f38,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f36,f69,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f131,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f86,f94])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f84,f71])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f74,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f38,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | k1_xboole_0 = sK0 | v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f102,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f69,f73,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    v4_relat_1(sK2,sK0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f38,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    sK1 = k2_relat_1(sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f70,f40])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f38,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f145,f164])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_xboole_0,sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f37,f144])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f206,f271])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f270,f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    k1_xboole_0 = k7_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f105,f164])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    k1_xboole_0 = k7_relat_1(k2_funct_1(sK2),k1_xboole_0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f95,f44])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f36,f69,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    k2_funct_1(k1_xboole_0) = k7_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f170,f196,f48])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    v4_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f182,f192])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    v4_relat_1(k2_funct_1(k1_xboole_0),sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f120,f164])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v4_relat_1(k2_funct_1(sK2),sK1)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f102,f53])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.49    inference(backward_demodulation,[],[f95,f164])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f205,f164])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f204,f192])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f203,f201])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.49    inference(forward_demodulation,[],[f189,f192])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f152,f164])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.49    inference(backward_demodulation,[],[f102,f144])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0)),
% 0.21/0.49    inference(forward_demodulation,[],[f191,f192])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0)),
% 0.21/0.49    inference(backward_demodulation,[],[f163,f164])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.21/0.49    inference(forward_demodulation,[],[f162,f144])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f148,f96])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    inference(backward_demodulation,[],[f41,f144])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (19198)------------------------------
% 0.21/0.49  % (19198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19198)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (19198)Memory used [KB]: 6268
% 0.21/0.49  % (19198)Time elapsed: 0.015 s
% 0.21/0.49  % (19198)------------------------------
% 0.21/0.49  % (19198)------------------------------
% 0.21/0.49  % (19194)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (19178)Success in time 0.133 s
%------------------------------------------------------------------------------
