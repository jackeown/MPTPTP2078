%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 234 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  324 (1891 expanded)
%              Number of equality atoms :   39 ( 164 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(subsumption_resolution,[],[f215,f118])).

fof(f118,plain,(
    k9_relat_1(sK3,sK4) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(resolution,[],[f66,f92])).

fof(f92,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f35,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(X4,u1_struct_0(X2))
                         => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(X4,u1_struct_0(X2))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK4) = k9_relat_1(X0,sK4) ) ),
    inference(resolution,[],[f31,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f31,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f215,plain,(
    k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(superposition,[],[f115,f180])).

fof(f180,plain,(
    ! [X2] : k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X2) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2) ),
    inference(resolution,[],[f155,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f155,plain,(
    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f138,f108])).

fof(f108,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f62,f40])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f37,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK1))
      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f106,f113])).

fof(f113,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK3,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f103,f51])).

fof(f103,plain,(
    ! [X1] : m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f94,f95])).

fof(f95,plain,(
    ! [X2] : k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2) = k9_relat_1(sK3,X2) ),
    inference(resolution,[],[f35,f45])).

fof(f94,plain,(
    ! [X1] : m1_subset_1(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f106,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k9_relat_1(sK3,X5),X6)
      | m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ r1_tarski(X5,u1_struct_0(sK1)) ) ),
    inference(backward_demodulation,[],[f99,f95])).

fof(f99,plain,(
    ! [X6,X5] :
      ( m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ r1_tarski(X5,u1_struct_0(sK1))
      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6) ) ),
    inference(backward_demodulation,[],[f89,f97])).

fof(f97,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f93,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f89,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,u1_struct_0(sK1))
      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6)
      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(subsumption_resolution,[],[f88,f35])).

fof(f88,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r1_tarski(X5,u1_struct_0(sK1))
      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6)
      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(subsumption_resolution,[],[f87,f65])).

fof(f65,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f64,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f59,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f43,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X6,X5] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r1_tarski(X5,u1_struct_0(sK1))
      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6)
      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f72,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ r1_tarski(X5,u1_struct_0(sK1))
      | ~ r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6)
      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X0,X3)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
      | m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          | ~ r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          | ~ r1_tarski(X1,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          | ~ v1_funct_2(X4,X0,X3)
          | ~ v1_funct_1(X4) )
      | v1_xboole_0(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          | ~ r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          | ~ r1_tarski(X1,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          | ~ v1_funct_2(X4,X0,X3)
          | ~ v1_funct_1(X4) )
      | v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f34,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,(
    k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(backward_demodulation,[],[f102,f114])).

fof(f114,plain,(
    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f98,f37])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) ) ),
    inference(backward_demodulation,[],[f80,f97])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f79,f35])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f78,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f76,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f75,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f74,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f69,f39])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X0,sK1)
      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f102,plain,(
    k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f32,f95])).

fof(f32,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:50:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (27296)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.48  % (27296)Refutation not found, incomplete strategy% (27296)------------------------------
% 0.22/0.48  % (27296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27315)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.48  % (27307)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.49  % (27313)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.49  % (27306)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.49  % (27302)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (27298)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (27296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (27296)Memory used [KB]: 10618
% 0.22/0.50  % (27296)Time elapsed: 0.072 s
% 0.22/0.50  % (27296)------------------------------
% 0.22/0.50  % (27296)------------------------------
% 0.22/0.50  % (27313)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f215,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    k9_relat_1(sK3,sK4) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.50    inference(resolution,[],[f66,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    v1_relat_1(sK3)),
% 0.22/0.50    inference(resolution,[],[f35,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK4) = k9_relat_1(X0,sK4)) )),
% 0.22/0.50    inference(resolution,[],[f31,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    r1_tarski(sK4,u1_struct_0(sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    k9_relat_1(sK3,sK4) != k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.50    inference(superposition,[],[f115,f180])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X2] : (k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X2) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X2)) )),
% 0.22/0.50    inference(resolution,[],[f155,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.22/0.50    inference(resolution,[],[f138,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.50    inference(resolution,[],[f63,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f62,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    l1_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.50    inference(resolution,[],[f37,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK1)) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))) )),
% 0.22/0.50    inference(resolution,[],[f106,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),u1_struct_0(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f103,f51])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X1] : (m1_subset_1(k9_relat_1(sK3,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f94,f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X2] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2) = k9_relat_1(sK3,X2)) )),
% 0.22/0.50    inference(resolution,[],[f35,f45])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X1] : (m1_subset_1(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.50    inference(resolution,[],[f35,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X6,X5] : (~r1_tarski(k9_relat_1(sK3,X5),X6) | m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~r1_tarski(X5,u1_struct_0(sK1))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f99,f95])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X6,X5] : (m1_subset_1(k7_relat_1(sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~r1_tarski(X5,u1_struct_0(sK1)) | ~r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f89,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X0] : (k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f93,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(sK3) | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.50    inference(resolution,[],[f35,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X6,X5] : (~r1_tarski(X5,u1_struct_0(sK1)) | ~r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f35])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X6,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tarski(X5,u1_struct_0(sK1)) | ~r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f87,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f64,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.50    inference(resolution,[],[f59,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f43,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ( ! [X6,X5] : (v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tarski(X5,u1_struct_0(sK1)) | ~r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f72,f33])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X6,X5] : (~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~r1_tarski(X5,u1_struct_0(sK1)) | ~r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),X6) | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 0.22/0.50    inference(resolution,[],[f34,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X0,X3) | ~v1_funct_1(X4) | v1_xboole_0(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~r1_tarski(X1,X0) | ~r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) | m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : ((m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))) | ~r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) | ~r1_tarski(X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_2(X4,X0,X3) | ~v1_funct_1(X4)) | v1_xboole_0(X3))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (! [X4] : (((m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))) | (~r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) | ~r1_tarski(X1,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_2(X4,X0,X3) | ~v1_funct_1(X4))) | v1_xboole_0(X3))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    k9_relat_1(sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f102,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.22/0.50    inference(resolution,[],[f98,f37])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f80,f97])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f79,f35])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f78,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f77,f33])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f76,f43])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f75,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f74,f41])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f73,f40])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f69,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    v2_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK3) | v2_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK1) | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))) )),
% 0.22/0.50    inference(resolution,[],[f34,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4)),
% 0.22/0.50    inference(backward_demodulation,[],[f32,f95])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (27313)------------------------------
% 0.22/0.50  % (27313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27313)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (27313)Memory used [KB]: 6268
% 0.22/0.50  % (27313)Time elapsed: 0.081 s
% 0.22/0.50  % (27313)------------------------------
% 0.22/0.50  % (27313)------------------------------
% 0.22/0.50  % (27288)Success in time 0.139 s
%------------------------------------------------------------------------------
