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
% DateTime   : Thu Dec  3 13:18:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 186 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   19
%              Number of atoms          :  343 (1984 expanded)
%              Number of equality atoms :   48 ( 144 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f63])).

fof(f63,plain,(
    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f62,f60])).

fof(f60,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,
    ( ~ v1_relat_1(sK4)
    | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5) ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5) ) ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f87,plain,(
    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5) ),
    inference(backward_demodulation,[],[f73,f86])).

fof(f86,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f36,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f84,f32])).

fof(f32,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X0,sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f83,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f81,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK3) ) ),
    inference(resolution,[],[f80,f34])).

fof(f34,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k7_relat_1(sK4,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3) ) ),
    inference(forward_demodulation,[],[f79,f65])).

fof(f65,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(subsumption_resolution,[],[f64,f29])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0) ) ),
    inference(resolution,[],[f50,f31])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f78,f30])).

% (4302)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
fof(f30,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f77,f29])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f74,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK3)
      | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f73,plain,(
    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(sK4,sK5) ),
    inference(backward_demodulation,[],[f28,f72])).

fof(f72,plain,(
    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f71,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f70,f59])).

fof(f59,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f57,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f57,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f55,f42])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f44,f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f70,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)
    | ~ l1_struct_0(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f69,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) ),
    inference(resolution,[],[f68,f26])).

fof(f26,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | v1_xboole_0(u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f67,f30])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK4)
      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0) ) ),
    inference(resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f28,plain,(
    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:19:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (4293)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.48  % (4301)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.49  % (4292)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (4301)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f87,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f62,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    v1_relat_1(sK4)),
% 0.22/0.49    inference(resolution,[],[f47,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~v1_relat_1(sK4) | k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) = k1_funct_1(sK4,sK5)),
% 0.22/0.49    inference(resolution,[],[f61,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_funct_1(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k7_relat_1(X0,u1_struct_0(sK2)),sK5) = k1_funct_1(X0,sK5)) )),
% 0.22/0.49    inference(resolution,[],[f48,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    r2_hidden(sK5,u1_struct_0(sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK2)),sK5) != k1_funct_1(sK4,sK5)),
% 0.22/0.49    inference(backward_demodulation,[],[f73,f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f85,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2,sK0) | k3_tmap_1(sK0,sK1,sK3,sK2,sK4) = k7_relat_1(sK4,u1_struct_0(sK2))),
% 0.22/0.49    inference(resolution,[],[f84,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f83,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X0] : (k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f82,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f81,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k7_relat_1(sK4,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK3,X0,sK4) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK3)) )),
% 0.22/0.49    inference(resolution,[],[f80,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_pre_topc(sK3,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(sK3,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k7_relat_1(sK4,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f79,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0] : (k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f64,f29])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(sK4) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k7_relat_1(sK4,X0)) )),
% 0.22/0.49    inference(resolution,[],[f50,f31])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f78,f30])).
% 0.22/0.50  % (4302)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f77,f29])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f76,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    l1_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f75,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v2_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f74,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | k3_tmap_1(X0,sK1,sK3,X1,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),sK4,u1_struct_0(X1))) )),
% 0.22/0.50    inference(resolution,[],[f46,f31])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) != k1_funct_1(sK4,sK5)),
% 0.22/0.50    inference(backward_demodulation,[],[f28,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f71,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ~v2_struct_0(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) | v2_struct_0(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f70,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    l1_struct_0(sK3)),
% 0.22/0.50    inference(resolution,[],[f57,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    l1_pre_topc(sK3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f55,f42])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.22/0.50    inference(resolution,[],[f44,f34])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5) | ~l1_struct_0(sK3) | v2_struct_0(sK3)),
% 0.22/0.50    inference(resolution,[],[f69,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) = k1_funct_1(sK4,sK5)),
% 0.22/0.50    inference(resolution,[],[f68,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f67,f30])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f29])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK4,X0)) )),
% 0.22/0.50    inference(resolution,[],[f49,f31])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK5) != k1_funct_1(k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4301)------------------------------
% 0.22/0.50  % (4301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4301)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4301)Memory used [KB]: 6268
% 0.22/0.50  % (4301)Time elapsed: 0.078 s
% 0.22/0.50  % (4301)------------------------------
% 0.22/0.50  % (4301)------------------------------
% 0.22/0.50  % (4284)Success in time 0.136 s
%------------------------------------------------------------------------------
