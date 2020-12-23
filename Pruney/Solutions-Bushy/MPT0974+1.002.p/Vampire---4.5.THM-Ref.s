%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0974+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 205 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  235 (1259 expanded)
%              Number of equality atoms :   81 ( 480 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f374,f242])).

fof(f242,plain,(
    sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f32,f240])).

fof(f240,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f234,f28])).

fof(f28,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK3,sK4) = k1_partfun1(sK0,sK1,X0,X1,sK3,sK4) ) ),
    inference(resolution,[],[f145,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f145,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k5_relat_1(sK3,sK4) = k1_partfun1(X14,X15,X16,X17,sK3,sK4) ) ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X24,X23,X21,X22,X20] :
      ( ~ v1_funct_1(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_partfun1(X21,X22,X23,X24,X20,sK4) = k5_relat_1(X20,sK4) ) ),
    inference(resolution,[],[f26,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f26,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f13])).

fof(f374,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f362,f182])).

fof(f182,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f177,f35])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ) ),
    inference(resolution,[],[f142,f28])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f141,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK3)
      | sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f140,f39])).

fof(f140,plain,
    ( ~ v1_relat_1(sK4)
    | sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f139,f95])).

fof(f95,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f93,f35])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f42,f29])).

fof(f29,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f139,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f135,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f135,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f90,f115])).

fof(f115,plain,(
    sK1 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f104,f29])).

fof(f104,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f35,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k2_relat_1(X0))
      | sK2 = k2_relat_1(k5_relat_1(X0,sK4))
      | ~ v1_relat_1(sK4)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f89,f88])).

fof(f88,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(forward_demodulation,[],[f76,f30])).

fof(f30,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f28,f41])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k2_relat_1(X0))
      | ~ v1_relat_1(sK4)
      | ~ v1_relat_1(X0)
      | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) ) ),
    inference(superposition,[],[f36,f87])).

fof(f87,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f75,f71])).

fof(f71,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f70,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f69,f28])).

fof(f69,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f27,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f27,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f362,plain,(
    k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f359,f41])).

fof(f359,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f357,f240])).

fof(f357,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f355,f28])).

fof(f355,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f211,f35])).

fof(f211,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | m1_subset_1(k1_partfun1(X14,X15,X16,X17,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X14,X17))) ) ),
    inference(resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X14,X12,X10,X13,X11] :
      ( ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(k1_partfun1(X11,X12,X13,X14,X10,sK4),k1_zfmisc_1(k2_zfmisc_1(X11,X14))) ) ),
    inference(resolution,[],[f26,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

%------------------------------------------------------------------------------
