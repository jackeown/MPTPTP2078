%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 499 expanded)
%              Number of leaves         :   13 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  397 (3217 expanded)
%              Number of equality atoms :   57 ( 347 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(subsumption_resolution,[],[f151,f148])).

fof(f148,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f132,f147])).

fof(f147,plain,(
    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f144,f145])).

fof(f145,plain,(
    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f131,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f92,f125])).

fof(f125,plain,(
    v1_funct_2(sK4,sK0,sK2) ),
    inference(forward_demodulation,[],[f124,f71])).

fof(f71,plain,(
    sK0 = k1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f70,f65])).

fof(f65,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f70,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f69,f67])).

fof(f67,plain,(
    v4_relat_1(sK4,sK0) ),
    inference(resolution,[],[f59,f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f69,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f124,plain,(
    v1_funct_2(sK4,k1_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f123,f65])).

fof(f123,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_2(sK4,k1_relat_1(sK4),sK2) ),
    inference(subsumption_resolution,[],[f119,f41])).

fof(f41,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f119,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | v1_funct_2(sK4,k1_relat_1(sK4),sK2) ),
    inference(resolution,[],[f115,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f115,plain,(
    r1_tarski(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f80,plain,(
    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) ),
    inference(forward_demodulation,[],[f78,f76])).

fof(f76,plain,(
    k2_relset_1(sK0,sK2,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f78,plain,(
    m1_subset_1(k2_relset_1(sK0,sK2,sK4),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,sK0,sK2)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f89,f41])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(resolution,[],[f61,f42])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f131,plain,(
    m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    inference(backward_demodulation,[],[f117,f130])).

fof(f130,plain,(
    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(resolution,[],[f95,f38])).

fof(f38,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK1)
      | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f94,f46])).

fof(f46,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X1] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,sK1)
      | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,sK1)
      | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(subsumption_resolution,[],[f90,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,sK1)
      | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1) ) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f117,plain,(
    m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0) ),
    inference(resolution,[],[f88,f38])).

fof(f88,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK1)
      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,(
    ! [X1] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,sK1)
      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f86,f44])).

fof(f86,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,sK1)
      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f83,f43])).

fof(f83,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(X1,sK1)
      | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0) ) ),
    inference(resolution,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f144,plain,(
    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(resolution,[],[f131,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f100,f125])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,sK0,sK2)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f96,f75])).

fof(f75,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f74,f39])).

fof(f74,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_partfun1(sK4,sK0) ),
    inference(subsumption_resolution,[],[f72,f47])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_partfun1(sK4,sK0) ),
    inference(resolution,[],[f50,f42])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f96,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,sK0,sK2)
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X0,sK0)
      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f132,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(backward_demodulation,[],[f40,f130])).

fof(f40,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f151,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(forward_demodulation,[],[f150,f130])).

fof(f150,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(resolution,[],[f137,f38])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f136,f39])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ v1_partfun1(sK4,sK0)
      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X0,sK1)
      | ~ v1_partfun1(sK4,sK0)
      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) ) ),
    inference(resolution,[],[f113,f42])).

fof(f113,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,sK1)
      | ~ v1_partfun1(X3,sK0)
      | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f112,f47])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( v1_xboole_0(sK0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ v1_partfun1(X3,sK0)
      | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f111,f44])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ v1_partfun1(X3,sK0)
      | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f110,f43])).

fof(f110,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ v1_partfun1(X3,sK0)
      | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5)) ) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f106,plain,(
    ! [X4,X5,X3] :
      ( v1_xboole_0(sK1)
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_2(sK3,sK1,sK0)
      | v1_xboole_0(sK0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4)))
      | ~ m1_subset_1(X5,sK1)
      | ~ v1_partfun1(X3,sK0)
      | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5)) ) ),
    inference(resolution,[],[f49,f45])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | v1_xboole_0(X0)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X1)
      | ~ v1_partfun1(X4,X0)
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      | ~ v1_partfun1(X4,X0)
                      | ~ m1_subset_1(X5,X1) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  | ~ v1_funct_1(X4) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              | ~ v1_funct_2(X3,X1,X0)
              | ~ v1_funct_1(X3) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (12911)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.46  % (12919)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (12921)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (12915)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (12918)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (12926)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (12921)Refutation not found, incomplete strategy% (12921)------------------------------
% 0.21/0.48  % (12921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12921)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12921)Memory used [KB]: 6268
% 0.21/0.48  % (12921)Time elapsed: 0.011 s
% 0.21/0.48  % (12921)------------------------------
% 0.21/0.48  % (12921)------------------------------
% 0.21/0.49  % (12926)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f151,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(backward_demodulation,[],[f132,f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(backward_demodulation,[],[f144,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(resolution,[],[f131,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    v1_funct_2(sK4,sK0,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f124,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v1_relat_1(sK4)),
% 0.21/0.49    inference(resolution,[],[f56,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    v4_relat_1(sK4,sK0)),
% 0.21/0.49    inference(resolution,[],[f59,f42])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v4_relat_1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.49    inference(resolution,[],[f54,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v1_partfun1(sK4,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    v1_funct_2(sK4,k1_relat_1(sK4),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f65])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~v1_relat_1(sK4) | v1_funct_2(sK4,k1_relat_1(sK4),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f119,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v1_funct_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | v1_funct_2(sK4,k1_relat_1(sK4),sK2)),
% 0.21/0.49    inference(resolution,[],[f115,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK4),sK2)),
% 0.21/0.49    inference(resolution,[],[f80,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f78,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK2,sK4) = k2_relat_1(sK4)),
% 0.21/0.49    inference(resolution,[],[f57,f42])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    m1_subset_1(k2_relset_1(sK0,sK2,sK4),k1_zfmisc_1(sK2))),
% 0.21/0.49    inference(resolution,[],[f58,f42])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f41])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.21/0.49    inference(resolution,[],[f61,f42])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.21/0.49    inference(backward_demodulation,[],[f117,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.21/0.49    inference(resolution,[],[f95,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_subset_1(sK5,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X1] : (v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | k3_funct_2(sK1,sK0,sK3,X1) = k1_funct_1(sK3,X1)) )),
% 0.21/0.49    inference(resolution,[],[f61,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    m1_subset_1(k3_funct_2(sK1,sK0,sK3,sK5),sK0)),
% 0.21/0.49    inference(resolution,[],[f88,f38])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f46])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X1] : (v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f44])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f43])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X1,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X1),sK0)) )),
% 0.21/0.49    inference(resolution,[],[f60,f45])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(resolution,[],[f131,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f125])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f47])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f41])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f39])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2) | ~v1_partfun1(sK4,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f47])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_partfun1(sK4,sK0)),
% 0.21/0.49    inference(resolution,[],[f50,f42])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_partfun1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) )),
% 0.21/0.49    inference(resolution,[],[f48,f42])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(backward_demodulation,[],[f40,f130])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(forward_demodulation,[],[f150,f130])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.49    inference(resolution,[],[f137,f38])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f39])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_partfun1(sK4,sK0) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f41])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(X0,sK1) | ~v1_partfun1(sK4,sK0) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) )),
% 0.21/0.49    inference(resolution,[],[f113,f42])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~v1_funct_1(X3) | ~m1_subset_1(X5,sK1) | ~v1_partfun1(X3,sK0) | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f47])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (v1_xboole_0(sK0) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~m1_subset_1(X5,sK1) | ~v1_partfun1(X3,sK0) | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f44])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~m1_subset_1(X5,sK1) | ~v1_partfun1(X3,sK0) | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f43])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~m1_subset_1(X5,sK1) | ~v1_partfun1(X3,sK0) | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f46])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (v1_xboole_0(sK1) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X4))) | ~m1_subset_1(X5,sK1) | ~v1_partfun1(X3,sK0) | k3_funct_2(sK1,X4,k8_funct_2(sK1,sK0,X4,sK3,X3),X5) = k1_funct_1(X3,k3_funct_2(sK1,sK0,sK3,X5))) )),
% 0.21/0.49    inference(resolution,[],[f49,f45])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | v1_xboole_0(X0) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X1) | ~v1_partfun1(X4,X0) | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2,X3] : (! [X4] : (! [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) | ~v1_partfun1(X4,X0)) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (12926)------------------------------
% 0.21/0.49  % (12926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12912)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (12926)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (12926)Memory used [KB]: 1791
% 0.21/0.49  % (12926)Time elapsed: 0.075 s
% 0.21/0.49  % (12926)------------------------------
% 0.21/0.49  % (12926)------------------------------
% 0.21/0.49  % (12908)Success in time 0.133 s
%------------------------------------------------------------------------------
