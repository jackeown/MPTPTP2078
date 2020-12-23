%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:30 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 483 expanded)
%              Number of leaves         :   18 (  91 expanded)
%              Depth                    :   19
%              Number of atoms          :  361 (2761 expanded)
%              Number of equality atoms :  108 ( 796 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f465,plain,(
    $false ),
    inference(subsumption_resolution,[],[f464,f137])).

fof(f137,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(superposition,[],[f54,f100])).

fof(f100,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

% (30959)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f464,plain,(
    sK1 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f463,f178])).

fof(f178,plain,(
    sK3 = k8_relat_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f174,f89])).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f57])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f174,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k8_relat_1(sK1,sK3) ),
    inference(resolution,[],[f136,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f136,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f135,f89])).

fof(f135,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f93,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f73,f57])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f463,plain,(
    sK1 = k2_relat_1(k8_relat_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f460,f89])).

fof(f460,plain,
    ( ~ v1_relat_1(sK3)
    | sK1 = k2_relat_1(k8_relat_1(sK1,sK3)) ),
    inference(resolution,[],[f418,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(f418,plain,(
    r1_tarski(sK1,k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f303,f417])).

fof(f417,plain,(
    sK2 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f140,f415])).

fof(f415,plain,(
    ~ r2_xboole_0(k2_relat_1(sK4),sK2) ),
    inference(superposition,[],[f202,f357])).

fof(f357,plain,(
    sK2 = k9_relat_1(sK4,k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f355,f301])).

fof(f301,plain,(
    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f286,f171])).

fof(f171,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f51,f169])).

fof(f169,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f167,f48])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f167,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f124,f50])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f124,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | k1_partfun1(sK0,sK1,X4,X5,sK3,X3) = k5_relat_1(sK3,X3) ) ),
    inference(subsumption_resolution,[],[f122,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f122,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_partfun1(sK0,sK1,X4,X5,sK3,X3) = k5_relat_1(sK3,X3) ) ),
    inference(resolution,[],[f80,f57])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f51,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f286,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(resolution,[],[f189,f71])).

fof(f189,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f188,f169])).

fof(f188,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f186,f48])).

fof(f186,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f128,f50])).

fof(f128,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) ) ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f126,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) ) ),
    inference(resolution,[],[f82,f57])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f355,plain,(
    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) ),
    inference(resolution,[],[f101,f88])).

fof(f88,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f69,f50])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f89,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f202,plain,(
    ! [X1] : ~ r2_xboole_0(k2_relat_1(sK4),k9_relat_1(sK4,X1)) ),
    inference(backward_demodulation,[],[f197,f198])).

fof(f198,plain,(
    k2_relat_1(sK4) = k9_relat_1(sK4,sK1) ),
    inference(superposition,[],[f95,f130])).

fof(f130,plain,(
    sK4 = k7_relat_1(sK4,sK1) ),
    inference(subsumption_resolution,[],[f129,f88])).

fof(f129,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK1) ),
    inference(resolution,[],[f90,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f90,plain,(
    v4_relat_1(sK4,sK1) ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X1] : k9_relat_1(sK4,X1) = k2_relat_1(k7_relat_1(sK4,X1)) ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f197,plain,(
    ! [X1] : ~ r2_xboole_0(k9_relat_1(sK4,sK1),k9_relat_1(sK4,X1)) ),
    inference(resolution,[],[f111,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f111,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,sK1)) ),
    inference(backward_demodulation,[],[f94,f110])).

fof(f110,plain,(
    sK1 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f97,f109])).

fof(f109,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f49,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f108,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ v1_funct_2(sK4,sK1,sK2) ),
    inference(subsumption_resolution,[],[f106,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ v1_funct_2(sK4,sK1,sK2) ),
    inference(resolution,[],[f79,f50])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f97,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f94,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4))) ),
    inference(resolution,[],[f88,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

fof(f140,plain,
    ( sK2 = k2_relat_1(sK4)
    | r2_xboole_0(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f134,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f134,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f133,f88])).

fof(f133,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f92,f65])).

fof(f92,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f73,f50])).

fof(f303,plain,
    ( sK2 != k2_relat_1(sK4)
    | r1_tarski(sK1,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f160,f301])).

fof(f160,plain,
    ( r1_tarski(sK1,k2_relat_1(sK3))
    | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(forward_demodulation,[],[f159,f110])).

fof(f159,plain,
    ( k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f158,f48])).

fof(f158,plain,
    ( k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f157,f88])).

fof(f157,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) ),
    inference(resolution,[],[f116,f52])).

fof(f52,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,(
    ! [X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) != k2_relat_1(k5_relat_1(sK3,X1))
      | ~ v1_funct_1(X1)
      | r1_tarski(k1_relat_1(X1),k2_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f114,f89])).

fof(f114,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) != k2_relat_1(k5_relat_1(sK3,X1))
      | ~ v2_funct_1(X1)
      | r1_tarski(k1_relat_1(X1),k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f59,f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v2_funct_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n019.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 11:46:22 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.13/0.34  % (30955)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.13/0.38  % (30957)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.13/0.38  % (30966)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.13/0.38  % (30952)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.13/0.38  % (30956)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.13/0.38  % (30948)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.13/0.39  % (30965)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.13/0.39  % (30963)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.13/0.40  % (30949)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.13/0.40  % (30961)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.13/0.40  % (30964)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.13/0.40  % (30969)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.13/0.41  % (30966)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % (30967)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.13/0.41  % (30958)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.13/0.42  % (30954)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f465,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(subsumption_resolution,[],[f464,f137])).
% 0.13/0.42  fof(f137,plain,(
% 0.13/0.42    sK1 != k2_relat_1(sK3)),
% 0.13/0.42    inference(superposition,[],[f54,f100])).
% 0.13/0.42  fof(f100,plain,(
% 0.13/0.42    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.13/0.42    inference(resolution,[],[f71,f57])).
% 0.13/0.42  fof(f57,plain,(
% 0.13/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.13/0.42    inference(flattening,[],[f21])).
% 0.13/0.42  fof(f21,plain,(
% 0.13/0.42    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.13/0.42    inference(ennf_transformation,[],[f19])).
% 0.13/0.42  fof(f19,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.13/0.42    inference(negated_conjecture,[],[f18])).
% 0.13/0.42  % (30959)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.13/0.42  fof(f18,conjecture,(
% 0.13/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 0.13/0.42  fof(f71,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f40])).
% 0.13/0.42  fof(f40,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f14])).
% 0.13/0.42  fof(f14,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.13/0.42  fof(f54,plain,(
% 0.13/0.42    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f464,plain,(
% 0.13/0.42    sK1 = k2_relat_1(sK3)),
% 0.13/0.42    inference(forward_demodulation,[],[f463,f178])).
% 0.13/0.42  fof(f178,plain,(
% 0.13/0.42    sK3 = k8_relat_1(sK1,sK3)),
% 0.13/0.42    inference(subsumption_resolution,[],[f174,f89])).
% 0.13/0.42  fof(f89,plain,(
% 0.13/0.42    v1_relat_1(sK3)),
% 0.13/0.42    inference(resolution,[],[f69,f57])).
% 0.13/0.42  fof(f69,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f38])).
% 0.13/0.42  fof(f38,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.13/0.42  fof(f174,plain,(
% 0.13/0.42    ~v1_relat_1(sK3) | sK3 = k8_relat_1(sK1,sK3)),
% 0.13/0.42    inference(resolution,[],[f136,f63])).
% 0.13/0.42  fof(f63,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.13/0.42    inference(cnf_transformation,[],[f31])).
% 0.13/0.42  fof(f31,plain,(
% 0.13/0.42    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(flattening,[],[f30])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.13/0.42  fof(f136,plain,(
% 0.13/0.42    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.13/0.42    inference(subsumption_resolution,[],[f135,f89])).
% 0.13/0.42  fof(f135,plain,(
% 0.13/0.42    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.13/0.42    inference(resolution,[],[f93,f65])).
% 0.13/0.42  fof(f65,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f32])).
% 0.13/0.42  fof(f32,plain,(
% 0.13/0.42    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.13/0.42  fof(f93,plain,(
% 0.13/0.42    v5_relat_1(sK3,sK1)),
% 0.13/0.42    inference(resolution,[],[f73,f57])).
% 0.13/0.42  fof(f73,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f41])).
% 0.13/0.42  fof(f41,plain,(
% 0.13/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f12])).
% 0.13/0.42  fof(f12,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.13/0.42  fof(f463,plain,(
% 0.13/0.42    sK1 = k2_relat_1(k8_relat_1(sK1,sK3))),
% 0.13/0.42    inference(subsumption_resolution,[],[f460,f89])).
% 0.13/0.42  fof(f460,plain,(
% 0.13/0.42    ~v1_relat_1(sK3) | sK1 = k2_relat_1(k8_relat_1(sK1,sK3))),
% 0.13/0.42    inference(resolution,[],[f418,f62])).
% 0.13/0.42  fof(f62,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = X0) )),
% 0.13/0.42    inference(cnf_transformation,[],[f29])).
% 0.13/0.42  fof(f29,plain,(
% 0.13/0.42    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(flattening,[],[f28])).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    ! [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).
% 0.13/0.42  fof(f418,plain,(
% 0.13/0.42    r1_tarski(sK1,k2_relat_1(sK3))),
% 0.13/0.42    inference(subsumption_resolution,[],[f303,f417])).
% 0.13/0.42  fof(f417,plain,(
% 0.13/0.42    sK2 = k2_relat_1(sK4)),
% 0.13/0.42    inference(subsumption_resolution,[],[f140,f415])).
% 0.13/0.42  fof(f415,plain,(
% 0.13/0.42    ~r2_xboole_0(k2_relat_1(sK4),sK2)),
% 0.13/0.42    inference(superposition,[],[f202,f357])).
% 0.13/0.42  fof(f357,plain,(
% 0.13/0.42    sK2 = k9_relat_1(sK4,k2_relat_1(sK3))),
% 0.13/0.42    inference(forward_demodulation,[],[f355,f301])).
% 0.13/0.42  fof(f301,plain,(
% 0.13/0.42    sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.13/0.42    inference(forward_demodulation,[],[f286,f171])).
% 0.13/0.42  fof(f171,plain,(
% 0.13/0.42    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.13/0.42    inference(backward_demodulation,[],[f51,f169])).
% 0.13/0.42  fof(f169,plain,(
% 0.13/0.42    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.13/0.42    inference(subsumption_resolution,[],[f167,f48])).
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    v1_funct_1(sK4)),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f167,plain,(
% 0.13/0.42    ~v1_funct_1(sK4) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.13/0.42    inference(resolution,[],[f124,f50])).
% 0.13/0.42  fof(f50,plain,(
% 0.13/0.42    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f124,plain,(
% 0.13/0.42    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | k1_partfun1(sK0,sK1,X4,X5,sK3,X3) = k5_relat_1(sK3,X3)) )),
% 0.13/0.42    inference(subsumption_resolution,[],[f122,f55])).
% 0.13/0.42  fof(f55,plain,(
% 0.13/0.42    v1_funct_1(sK3)),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f122,plain,(
% 0.13/0.42    ( ! [X4,X5,X3] : (~v1_funct_1(sK3) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | k1_partfun1(sK0,sK1,X4,X5,sK3,X3) = k5_relat_1(sK3,X3)) )),
% 0.13/0.42    inference(resolution,[],[f80,f57])).
% 0.13/0.42  fof(f80,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f45])).
% 0.13/0.42  fof(f45,plain,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.13/0.42    inference(flattening,[],[f44])).
% 0.13/0.42  fof(f44,plain,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.13/0.42    inference(ennf_transformation,[],[f17])).
% 0.13/0.42  fof(f17,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.13/0.42  fof(f51,plain,(
% 0.13/0.42    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f286,plain,(
% 0.13/0.42    k2_relat_1(k5_relat_1(sK3,sK4)) = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.13/0.42    inference(resolution,[],[f189,f71])).
% 0.13/0.42  fof(f189,plain,(
% 0.13/0.42    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.13/0.42    inference(forward_demodulation,[],[f188,f169])).
% 0.13/0.42  fof(f188,plain,(
% 0.13/0.42    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.13/0.42    inference(subsumption_resolution,[],[f186,f48])).
% 0.13/0.42  fof(f186,plain,(
% 0.13/0.42    ~v1_funct_1(sK4) | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.13/0.42    inference(resolution,[],[f128,f50])).
% 0.13/0.42  fof(f128,plain,(
% 0.13/0.42    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))) )),
% 0.13/0.42    inference(subsumption_resolution,[],[f126,f55])).
% 0.13/0.42  fof(f126,plain,(
% 0.13/0.42    ( ! [X4,X5,X3] : (~v1_funct_1(sK3) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5)))) )),
% 0.13/0.42    inference(resolution,[],[f82,f57])).
% 0.13/0.42  fof(f82,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f47])).
% 0.13/0.42  fof(f47,plain,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.13/0.42    inference(flattening,[],[f46])).
% 0.13/0.42  fof(f46,plain,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.13/0.42    inference(ennf_transformation,[],[f16])).
% 0.13/0.42  fof(f16,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.13/0.42  fof(f355,plain,(
% 0.13/0.42    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))),
% 0.13/0.42    inference(resolution,[],[f101,f88])).
% 0.13/0.42  fof(f88,plain,(
% 0.13/0.42    v1_relat_1(sK4)),
% 0.13/0.42    inference(resolution,[],[f69,f50])).
% 0.13/0.42  fof(f101,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,k2_relat_1(sK3))) )),
% 0.13/0.42    inference(resolution,[],[f89,f58])).
% 0.13/0.42  fof(f58,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f23])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f8])).
% 0.13/0.42  fof(f8,axiom,(
% 0.13/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.13/0.42  fof(f202,plain,(
% 0.13/0.42    ( ! [X1] : (~r2_xboole_0(k2_relat_1(sK4),k9_relat_1(sK4,X1))) )),
% 0.13/0.42    inference(backward_demodulation,[],[f197,f198])).
% 0.13/0.42  fof(f198,plain,(
% 0.13/0.42    k2_relat_1(sK4) = k9_relat_1(sK4,sK1)),
% 0.13/0.42    inference(superposition,[],[f95,f130])).
% 0.13/0.42  fof(f130,plain,(
% 0.13/0.42    sK4 = k7_relat_1(sK4,sK1)),
% 0.13/0.42    inference(subsumption_resolution,[],[f129,f88])).
% 0.13/0.42  fof(f129,plain,(
% 0.13/0.42    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK1)),
% 0.13/0.42    inference(resolution,[],[f90,f66])).
% 0.13/0.42  fof(f66,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.13/0.42    inference(cnf_transformation,[],[f34])).
% 0.13/0.42  fof(f34,plain,(
% 0.13/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(flattening,[],[f33])).
% 0.13/0.42  fof(f33,plain,(
% 0.13/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.13/0.42    inference(ennf_transformation,[],[f9])).
% 0.13/0.42  fof(f9,axiom,(
% 0.13/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.13/0.42  fof(f90,plain,(
% 0.13/0.42    v4_relat_1(sK4,sK1)),
% 0.13/0.42    inference(resolution,[],[f72,f50])).
% 0.13/0.42  fof(f72,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f41])).
% 0.13/0.42  fof(f95,plain,(
% 0.13/0.42    ( ! [X1] : (k9_relat_1(sK4,X1) = k2_relat_1(k7_relat_1(sK4,X1))) )),
% 0.13/0.42    inference(resolution,[],[f88,f60])).
% 0.13/0.42  fof(f60,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f26])).
% 0.13/0.42  fof(f26,plain,(
% 0.13/0.42    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f7])).
% 0.13/0.42  fof(f7,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.13/0.42  fof(f197,plain,(
% 0.13/0.42    ( ! [X1] : (~r2_xboole_0(k9_relat_1(sK4,sK1),k9_relat_1(sK4,X1))) )),
% 0.13/0.42    inference(resolution,[],[f111,f68])).
% 0.13/0.42  fof(f68,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f37])).
% 0.13/0.42  fof(f37,plain,(
% 0.13/0.42    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.13/0.42  fof(f111,plain,(
% 0.13/0.42    ( ! [X0] : (r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,sK1))) )),
% 0.13/0.42    inference(backward_demodulation,[],[f94,f110])).
% 0.13/0.42  fof(f110,plain,(
% 0.13/0.42    sK1 = k1_relat_1(sK4)),
% 0.13/0.42    inference(backward_demodulation,[],[f97,f109])).
% 0.13/0.42  fof(f109,plain,(
% 0.13/0.42    sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.13/0.42    inference(subsumption_resolution,[],[f108,f49])).
% 0.13/0.42  fof(f49,plain,(
% 0.13/0.42    v1_funct_2(sK4,sK1,sK2)),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f108,plain,(
% 0.13/0.42    sK1 = k1_relset_1(sK1,sK2,sK4) | ~v1_funct_2(sK4,sK1,sK2)),
% 0.13/0.42    inference(subsumption_resolution,[],[f106,f53])).
% 0.13/0.42  fof(f53,plain,(
% 0.13/0.42    k1_xboole_0 != sK2),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f106,plain,(
% 0.13/0.42    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4) | ~v1_funct_2(sK4,sK1,sK2)),
% 0.13/0.42    inference(resolution,[],[f79,f50])).
% 0.13/0.42  fof(f79,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f43])).
% 0.13/0.42  fof(f43,plain,(
% 0.13/0.42    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(flattening,[],[f42])).
% 0.13/0.42  fof(f42,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f15])).
% 0.13/0.42  fof(f15,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.13/0.42  fof(f97,plain,(
% 0.13/0.42    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 0.13/0.42    inference(resolution,[],[f70,f50])).
% 0.13/0.42  fof(f70,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f39])).
% 0.13/0.42  fof(f39,plain,(
% 0.13/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.13/0.42    inference(ennf_transformation,[],[f13])).
% 0.13/0.42  fof(f13,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.13/0.42  fof(f94,plain,(
% 0.13/0.42    ( ! [X0] : (r1_tarski(k9_relat_1(sK4,X0),k9_relat_1(sK4,k1_relat_1(sK4)))) )),
% 0.13/0.42    inference(resolution,[],[f88,f61])).
% 0.13/0.42  fof(f61,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f27])).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f6])).
% 0.13/0.42  fof(f6,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).
% 0.13/0.42  fof(f140,plain,(
% 0.13/0.42    sK2 = k2_relat_1(sK4) | r2_xboole_0(k2_relat_1(sK4),sK2)),
% 0.13/0.42    inference(resolution,[],[f134,f67])).
% 0.13/0.42  fof(f67,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f36])).
% 0.13/0.42  fof(f36,plain,(
% 0.13/0.42    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.13/0.42    inference(flattening,[],[f35])).
% 0.13/0.42  fof(f35,plain,(
% 0.13/0.42    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.13/0.42    inference(ennf_transformation,[],[f20])).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.13/0.42    inference(unused_predicate_definition_removal,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.13/0.42  fof(f134,plain,(
% 0.13/0.42    r1_tarski(k2_relat_1(sK4),sK2)),
% 0.13/0.42    inference(subsumption_resolution,[],[f133,f88])).
% 0.13/0.42  fof(f133,plain,(
% 0.13/0.42    r1_tarski(k2_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 0.13/0.42    inference(resolution,[],[f92,f65])).
% 0.13/0.42  fof(f92,plain,(
% 0.13/0.42    v5_relat_1(sK4,sK2)),
% 0.13/0.42    inference(resolution,[],[f73,f50])).
% 0.13/0.42  fof(f303,plain,(
% 0.13/0.42    sK2 != k2_relat_1(sK4) | r1_tarski(sK1,k2_relat_1(sK3))),
% 0.13/0.42    inference(backward_demodulation,[],[f160,f301])).
% 0.13/0.42  fof(f160,plain,(
% 0.13/0.42    r1_tarski(sK1,k2_relat_1(sK3)) | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.13/0.42    inference(forward_demodulation,[],[f159,f110])).
% 0.13/0.42  fof(f159,plain,(
% 0.13/0.42    k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) | r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))),
% 0.13/0.42    inference(subsumption_resolution,[],[f158,f48])).
% 0.13/0.42  fof(f158,plain,(
% 0.13/0.42    k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK4) | r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))),
% 0.13/0.42    inference(subsumption_resolution,[],[f157,f88])).
% 0.13/0.42  fof(f157,plain,(
% 0.13/0.42    ~v1_relat_1(sK4) | k2_relat_1(sK4) != k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK4) | r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))),
% 0.13/0.42    inference(resolution,[],[f116,f52])).
% 0.13/0.42  fof(f52,plain,(
% 0.13/0.42    v2_funct_1(sK4)),
% 0.13/0.42    inference(cnf_transformation,[],[f22])).
% 0.13/0.42  fof(f116,plain,(
% 0.13/0.42    ( ! [X1] : (~v2_funct_1(X1) | ~v1_relat_1(X1) | k2_relat_1(X1) != k2_relat_1(k5_relat_1(sK3,X1)) | ~v1_funct_1(X1) | r1_tarski(k1_relat_1(X1),k2_relat_1(sK3))) )),
% 0.13/0.42    inference(subsumption_resolution,[],[f114,f89])).
% 0.13/0.42  fof(f114,plain,(
% 0.13/0.42    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(sK3) | ~v1_relat_1(X1) | k2_relat_1(X1) != k2_relat_1(k5_relat_1(sK3,X1)) | ~v2_funct_1(X1) | r1_tarski(k1_relat_1(X1),k2_relat_1(sK3))) )),
% 0.13/0.42    inference(resolution,[],[f59,f55])).
% 0.13/0.42  fof(f59,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v2_funct_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f25])).
% 0.13/0.42  fof(f25,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(flattening,[],[f24])).
% 0.13/0.42  fof(f24,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.13/0.42    inference(ennf_transformation,[],[f10])).
% 0.13/0.42  fof(f10,axiom,(
% 0.13/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (30966)------------------------------
% 0.13/0.42  % (30966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (30966)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (30966)Memory used [KB]: 2046
% 0.13/0.42  % (30966)Time elapsed: 0.060 s
% 0.13/0.42  % (30966)------------------------------
% 0.13/0.42  % (30966)------------------------------
% 0.13/0.42  % (30950)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.13/0.42  % (30949)Refutation not found, incomplete strategy% (30949)------------------------------
% 0.13/0.42  % (30949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (30949)Termination reason: Refutation not found, incomplete strategy
% 0.13/0.42  
% 0.13/0.42  % (30949)Memory used [KB]: 10874
% 0.13/0.42  % (30949)Time elapsed: 0.080 s
% 0.13/0.42  % (30949)------------------------------
% 0.13/0.42  % (30949)------------------------------
% 0.13/0.42  % (30946)Success in time 0.136 s
%------------------------------------------------------------------------------
