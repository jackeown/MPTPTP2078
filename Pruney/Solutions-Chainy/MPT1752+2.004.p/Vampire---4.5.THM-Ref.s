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
% DateTime   : Thu Dec  3 13:18:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 283 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  303 (2485 expanded)
%              Number of equality atoms :   41 ( 213 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(subsumption_resolution,[],[f190,f87])).

fof(f87,plain,(
    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(subsumption_resolution,[],[f86,f78])).

fof(f78,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f30,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

% (13192)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                       => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tmap_1)).

fof(f86,plain,
    ( ~ v1_relat_1(sK3)
    | k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(subsumption_resolution,[],[f85,f28])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(resolution,[],[f83,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f83,plain,(
    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f26,f80])).

fof(f80,plain,(
    ! [X1] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X1) = k10_relat_1(sK3,X1) ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f26,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f190,plain,(
    k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(superposition,[],[f94,f168])).

fof(f168,plain,(
    ! [X1] : k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),X1) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1) ),
    inference(resolution,[],[f141,f44])).

fof(f141,plain,(
    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f140,f92])).

fof(f92,plain,(
    k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f82,f32])).

fof(f32,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0)) ) ),
    inference(backward_demodulation,[],[f65,f81])).

fof(f81,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(subsumption_resolution,[],[f79,f28])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f34,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f58,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f54,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK3)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f29,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f140,plain,(
    m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(resolution,[],[f77,f53])).

fof(f53,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f52,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f51,f38])).

fof(f51,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f77,plain,(
    ! [X3] :
      ( ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f76,f30])).

fof(f76,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f75,f50])).

fof(f50,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f46])).

fof(f75,plain,(
    ! [X3] :
      ( ~ l1_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f74,f28])).

fof(f74,plain,(
    ! [X3] :
      ( ~ v1_funct_1(sK3)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) ) ),
    inference(subsumption_resolution,[],[f57,f49])).

fof(f49,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f35,f46])).

fof(f57,plain,(
    ! [X3] :
      ( ~ l1_struct_0(sK1)
      | ~ v1_funct_1(sK3)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) ) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f94,plain,(
    k10_relat_1(sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    inference(backward_demodulation,[],[f84,f92])).

fof(f84,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4) ),
    inference(backward_demodulation,[],[f27,f80])).

fof(f27,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:48:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13188)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (13186)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (13182)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (13205)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.50  % (13187)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (13183)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (13194)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (13203)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (13197)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (13198)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (13196)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (13202)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (13204)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (13184)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (13190)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (13195)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (13193)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (13201)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (13198)Refutation not found, incomplete strategy% (13198)------------------------------
% 0.22/0.52  % (13198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13189)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (13202)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (13191)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (13190)Refutation not found, incomplete strategy% (13190)------------------------------
% 0.22/0.52  % (13190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13205)Refutation not found, incomplete strategy% (13205)------------------------------
% 0.22/0.52  % (13205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13205)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13205)Memory used [KB]: 10618
% 0.22/0.52  % (13205)Time elapsed: 0.064 s
% 0.22/0.52  % (13205)------------------------------
% 0.22/0.52  % (13205)------------------------------
% 0.22/0.53  % (13189)Refutation not found, incomplete strategy% (13189)------------------------------
% 0.22/0.53  % (13189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13189)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13189)Memory used [KB]: 6268
% 0.22/0.53  % (13189)Time elapsed: 0.067 s
% 0.22/0.53  % (13189)------------------------------
% 0.22/0.53  % (13189)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f190,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f86,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f30,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  % (13192)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tmap_1)).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ~v1_relat_1(sK3) | k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f85,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.53    inference(resolution,[],[f83,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))),
% 0.22/0.53    inference(backward_demodulation,[],[f26,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X1] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X1) = k10_relat_1(sK3,X1)) )),
% 0.22/0.53    inference(resolution,[],[f30,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.53    inference(superposition,[],[f94,f168])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ( ! [X1] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),X1) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X1)) )),
% 0.22/0.53    inference(resolution,[],[f141,f44])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.53    inference(forward_demodulation,[],[f140,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 0.22/0.53    inference(resolution,[],[f82,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(backward_demodulation,[],[f65,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f79,f28])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK3) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.53    inference(resolution,[],[f30,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f64,f30])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f63,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f62,f28])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f61,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f60,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    v2_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f59,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ~v2_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f58,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f54,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK3) | v2_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(resolution,[],[f29,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.53    inference(resolution,[],[f77,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    l1_struct_0(sK2)),
% 0.22/0.53    inference(resolution,[],[f52,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    l1_pre_topc(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f51,f38])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.53    inference(resolution,[],[f32,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X3] : (~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f76,f30])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f75,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    l1_struct_0(sK0)),
% 0.22/0.53    inference(resolution,[],[f38,f46])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X3] : (~l1_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f74,f28])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X3] : (~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f57,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    l1_struct_0(sK1)),
% 0.22/0.53    inference(resolution,[],[f35,f46])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X3] : (~l1_struct_0(sK1) | ~v1_funct_1(sK3) | ~l1_struct_0(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))) )),
% 0.22/0.53    inference(resolution,[],[f29,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    k10_relat_1(sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 0.22/0.53    inference(backward_demodulation,[],[f84,f92])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4)),
% 0.22/0.53    inference(backward_demodulation,[],[f27,f80])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (13202)------------------------------
% 0.22/0.53  % (13202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13202)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (13202)Memory used [KB]: 6268
% 0.22/0.53  % (13202)Time elapsed: 0.109 s
% 0.22/0.53  % (13202)------------------------------
% 0.22/0.53  % (13202)------------------------------
% 0.22/0.53  % (13180)Success in time 0.163 s
%------------------------------------------------------------------------------
