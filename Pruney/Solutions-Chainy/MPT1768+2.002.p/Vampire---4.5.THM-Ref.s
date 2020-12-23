%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 (1202 expanded)
%              Number of leaves         :    9 ( 217 expanded)
%              Depth                    :   43
%              Number of atoms          : 1037 (13421 expanded)
%              Number of equality atoms :   78 ( 158 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(subsumption_resolution,[],[f233,f37])).

% (2363)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X3,X2) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f233,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f232,f34])).

fof(f34,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f232,plain,
    ( ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f231,f29])).

fof(f29,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f231,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f230,f28])).

fof(f28,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f230,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f229,f27])).

fof(f27,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f229,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f228,f33])).

fof(f33,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f228,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f227,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f227,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f226,f88])).

fof(f88,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f87,f79])).

fof(f79,plain,(
    v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f78,f43])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f72,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f87,plain,
    ( ~ v2_pre_topc(sK2)
    | m1_pre_topc(sK4,sK2) ),
    inference(subsumption_resolution,[],[f85,f64])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f61,f44])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f85,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | m1_pre_topc(sK4,sK2) ),
    inference(resolution,[],[f81,f33])).

fof(f81,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | m1_pre_topc(sK4,X1) ) ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f226,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f225,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f225,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f224,f41])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f223,f40])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f223,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f222,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f222,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f221,f64])).

fof(f221,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f220,f79])).

% (2366)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f220,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f219,f218])).

fof(f218,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(backward_demodulation,[],[f138,f217])).

fof(f217,plain,(
    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(subsumption_resolution,[],[f216,f44])).

fof(f216,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f215,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f215,plain,
    ( v2_struct_0(sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f211,f43])).

fof(f211,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f201,f36])).

fof(f36,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f201,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK3,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(X1,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f200,f165])).

fof(f165,plain,(
    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f164,f63])).

fof(f63,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f60,f44])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f46,f36])).

fof(f164,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f163,f77])).

fof(f77,plain,(
    v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f76,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f71,f44])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[],[f50,f36])).

fof(f163,plain,
    ( ~ v2_pre_topc(sK3)
    | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f155,f35])).

fof(f155,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f151,f34])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f150,f67])).

fof(f67,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f64,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f149,f28])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f148,f27])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f147,f41])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f146,f40])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f143,f39])).

fof(f143,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f142,f29])).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f141,f45])).

fof(f141,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f140,f45])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f115,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f115,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ~ v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X5,X1)
      | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X5,X1)
      | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f113,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X5,X1)
      | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5))
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f104,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(k2_tmap_1(X3,X2,X4,X1))
      | ~ v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X5,X1)
      | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5))
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f49,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f200,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X1)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(X1,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f193,f66])).

fof(f66,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f63,f45])).

fof(f193,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(sK3,X1)
      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(X1,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(sK3) ) ),
    inference(resolution,[],[f189,f34])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f188,f67])).

% (2364)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f187,f28])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2))
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f186,f27])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f185,f41])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f184,f40])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f181,f39])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,X0)
      | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2))
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ l1_pre_topc(X1)
      | ~ l1_struct_0(X0)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f180,f29])).

fof(f180,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,k2_tmap_1(X4,X1,X5,X2)) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X4,X1,X5,X2),u1_struct_0(X3))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f179,f45])).

fof(f179,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,k2_tmap_1(X4,X1,X5,X2)) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X4,X1,X5,X2),u1_struct_0(X3))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,k2_tmap_1(X4,X1,X5,X2)) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X4,X1,X5,X2),u1_struct_0(X3))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(X4) ) ),
    inference(resolution,[],[f128,f53])).

fof(f128,plain,(
    ! [X6,X4,X2,X7,X5,X3] :
      ( ~ v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3))
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X5,X4)
      | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3))))
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f127,plain,(
    ! [X6,X4,X2,X7,X5,X3] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X2)
      | ~ v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X5,X4)
      | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5))
      | ~ l1_struct_0(X3)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3))))
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f126,f51])).

fof(f126,plain,(
    ! [X6,X4,X2,X7,X5,X3] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X2)
      | ~ m1_pre_topc(X5,X2)
      | ~ v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X5,X4)
      | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5))
      | ~ l1_struct_0(X3)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3))))
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f119,f52])).

fof(f119,plain,(
    ! [X6,X4,X2,X7,X5,X3] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ m1_pre_topc(X4,X2)
      | ~ m1_pre_topc(X5,X2)
      | ~ v1_funct_1(k2_tmap_1(X6,X3,X7,X4))
      | ~ v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X5,X4)
      | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5))
      | ~ l1_struct_0(X3)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3))))
      | ~ l1_struct_0(X4)
      | ~ l1_struct_0(X6) ) ),
    inference(resolution,[],[f47,f54])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f138,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(backward_demodulation,[],[f136,f137])).

fof(f137,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(forward_demodulation,[],[f134,f117])).

fof(f117,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f112,f33])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f111,f37])).

fof(f111,plain,(
    ! [X0] :
      ( v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f110,f28])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f109,f27])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f108,f41])).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f107,f40])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f106,f39])).

fof(f106,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f105,f64])).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f103,f79])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f49,f29])).

fof(f134,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f132,f33])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f131,f42])).

fof(f131,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f130,f43])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(subsumption_resolution,[],[f129,f44])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5) ) ),
    inference(resolution,[],[f125,f38])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f124,f51])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f123,f28])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f122,f27])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f121,f41])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f118,f39])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,sK2)
      | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f47,f29])).

fof(f136,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k2_tmap_1(sK2,sK1,sK5,sK4)) ),
    inference(backward_demodulation,[],[f30,f135])).

fof(f135,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(forward_demodulation,[],[f133,f116])).

fof(f116,plain,(
    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f112,f88])).

fof(f133,plain,(
    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) ),
    inference(resolution,[],[f132,f88])).

fof(f30,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f219,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4,sK3)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f48,f214])).

fof(f214,plain,(
    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(subsumption_resolution,[],[f213,f64])).

fof(f213,plain,
    ( k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f212,f37])).

fof(f212,plain,
    ( v2_struct_0(sK2)
    | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f210,f79])).

fof(f210,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f201,f33])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (2362)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (2377)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.48  % (2367)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.48  % (2377)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (2378)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f233,f37])).
% 0.20/0.50  % (2363)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~v2_struct_0(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f232,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    m1_pre_topc(sK4,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f231,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f230,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f229,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    v1_funct_1(sK5)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f229,plain,(
% 0.20/0.50    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f228,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    m1_pre_topc(sK3,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f227,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ~v2_struct_0(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f226,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    m1_pre_topc(sK4,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f87,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    v2_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f78,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f72,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK2)),
% 0.20/0.50    inference(resolution,[],[f50,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ~v2_pre_topc(sK2) | m1_pre_topc(sK4,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f85,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    l1_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f61,f44])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.20/0.50    inference(resolution,[],[f46,f38])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | m1_pre_topc(sK4,sK2)),
% 0.20/0.50    inference(resolution,[],[f81,f33])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | m1_pre_topc(sK4,X1)) )),
% 0.20/0.50    inference(resolution,[],[f51,f34])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | m1_pre_topc(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f225,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ~v2_struct_0(sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f224,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    l1_pre_topc(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    ~l1_pre_topc(sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f223,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    v2_pre_topc(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f222,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f221,f64])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f220,f79])).
% 0.20/0.50  % (2366)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f219,f218])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 0.20/0.50    inference(backward_demodulation,[],[f138,f217])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f216,f44])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f215,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f211,f43])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) | ~l1_pre_topc(sK0)),
% 0.20/0.50    inference(resolution,[],[f201,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    m1_pre_topc(sK3,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_pre_topc(sK3,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(X1,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(X1)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f200,f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4))),
% 0.20/0.50    inference(subsumption_resolution,[],[f164,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    l1_pre_topc(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f60,f44])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.20/0.50    inference(resolution,[],[f46,f36])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f163,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    v2_pre_topc(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f76,f43])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f44])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK3)),
% 0.20/0.50    inference(resolution,[],[f50,f36])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ~v2_pre_topc(sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f155,f35])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    v2_struct_0(sK3) | ~v2_pre_topc(sK3) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) | ~l1_pre_topc(sK3)),
% 0.20/0.50    inference(resolution,[],[f151,f34])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f150,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    l1_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f64,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f149,f28])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f148,f27])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f147,f41])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f146,f40])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f143,f39])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | k2_tmap_1(X0,sK1,k2_tmap_1(sK2,sK1,sK5,X0),X1) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X1)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f142,f29])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~l1_struct_0(X3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f141,f45])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f140,f45])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X0) | k2_tmap_1(X0,X1,k2_tmap_1(X3,X1,X4,X0),X2) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X3,X1,X4,X0),u1_struct_0(X2)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~l1_struct_0(X3)) )),
% 0.20/0.50    inference(resolution,[],[f115,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X4,X2,X5,X3,X1] : (~v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X5,X1) | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~l1_struct_0(X3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f114,f45])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X4,X2,X5,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2)) | v2_struct_0(X1) | ~m1_pre_topc(X5,X1) | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~l1_struct_0(X1) | ~l1_struct_0(X3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f113,f45])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X4,X2,X5,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2)) | v2_struct_0(X1) | ~m1_pre_topc(X5,X1) | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5)) | ~l1_struct_0(X2) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~l1_struct_0(X1) | ~l1_struct_0(X3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f104,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0) | ~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X4,X2,X5,X3,X1] : (~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(k2_tmap_1(X3,X2,X4,X1)) | ~v1_funct_2(k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X1),u1_struct_0(X2)) | v2_struct_0(X1) | ~m1_pre_topc(X5,X1) | k2_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),k2_tmap_1(X3,X2,X4,X1),u1_struct_0(X5)) | ~l1_struct_0(X2) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) | ~l1_struct_0(X1) | ~l1_struct_0(X3)) )),
% 0.20/0.50    inference(resolution,[],[f49,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X1) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(X1,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f193,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    l1_struct_0(sK3)),
% 0.20/0.50    inference(resolution,[],[f63,f45])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X1) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(X1,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(X1) | ~l1_struct_0(sK3)) )),
% 0.20/0.50    inference(resolution,[],[f189,f34])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2)) | ~l1_pre_topc(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f188,f67])).
% 0.20/0.50  % (2364)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2)) | ~l1_pre_topc(X1) | ~l1_struct_0(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f187,f28])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2)) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X1) | ~l1_struct_0(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f186,f27])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X1) | ~l1_struct_0(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f185,f41])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(sK1) | ~m1_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X1) | ~l1_struct_0(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f184,f40])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X1) | ~l1_struct_0(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f181,f39])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X0,X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | k3_tmap_1(X1,sK1,X0,X2,k2_tmap_1(sK2,sK1,sK5,X0)) = k2_partfun1(u1_struct_0(X0),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,X0),u1_struct_0(X2)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(X1) | ~l1_struct_0(X0) | ~l1_struct_0(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f180,f29])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,k2_tmap_1(X4,X1,X5,X2)) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X4,X1,X5,X2),u1_struct_0(X3)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~l1_struct_0(X2) | ~l1_struct_0(X4)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f179,f45])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,k2_tmap_1(X4,X1,X5,X2)) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X4,X1,X5,X2),u1_struct_0(X3)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~l1_struct_0(X2) | ~l1_struct_0(X4) | ~l1_struct_0(X1)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,k2_tmap_1(X4,X1,X5,X2)) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X4,X1,X5,X2),u1_struct_0(X3)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~l1_struct_0(X2) | ~l1_struct_0(X4) | ~l1_struct_0(X1) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~l1_struct_0(X2) | ~l1_struct_0(X4)) )),
% 0.20/0.50    inference(resolution,[],[f128,f53])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X7,X5,X3] : (~v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3)) | ~l1_pre_topc(X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(X4,X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X5,X4) | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3)))) | ~l1_struct_0(X4) | ~l1_struct_0(X6)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f127,f45])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X7,X5,X3] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(X4,X2) | ~v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3)) | v2_struct_0(X2) | ~m1_pre_topc(X5,X4) | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5)) | ~l1_struct_0(X3) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3)))) | ~l1_struct_0(X4) | ~l1_struct_0(X6)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f126,f51])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X7,X5,X3] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(X4,X2) | ~m1_pre_topc(X5,X2) | ~v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3)) | v2_struct_0(X2) | ~m1_pre_topc(X5,X4) | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5)) | ~l1_struct_0(X3) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3)))) | ~l1_struct_0(X4) | ~l1_struct_0(X6)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f52])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X6,X4,X2,X7,X5,X3] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~m1_pre_topc(X4,X2) | ~m1_pre_topc(X5,X2) | ~v1_funct_1(k2_tmap_1(X6,X3,X7,X4)) | ~v1_funct_2(k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X4),u1_struct_0(X3)) | v2_struct_0(X2) | ~m1_pre_topc(X5,X4) | k3_tmap_1(X2,X3,X4,X5,k2_tmap_1(X6,X3,X7,X4)) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X3),k2_tmap_1(X6,X3,X7,X4),u1_struct_0(X5)) | ~l1_struct_0(X3) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(X6),u1_struct_0(X3)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X3)))) | ~l1_struct_0(X4) | ~l1_struct_0(X6)) )),
% 0.20/0.50    inference(resolution,[],[f47,f54])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 0.20/0.50    inference(backward_demodulation,[],[f136,f137])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)),
% 0.20/0.50    inference(forward_demodulation,[],[f134,f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    k2_tmap_1(sK2,sK1,sK5,sK3) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 0.20/0.50    inference(resolution,[],[f112,f33])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f111,f37])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f110,f28])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f27])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f41])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f40])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f106,f39])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f64])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f103,f79])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK1,sK5,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0))) )),
% 0.20/0.50    inference(resolution,[],[f49,f29])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3))),
% 0.20/0.50    inference(resolution,[],[f132,f33])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f131,f42])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f130,f43])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f129,f44])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0)) = k3_tmap_1(sK0,sK1,sK2,X0,sK5)) )),
% 0.20/0.50    inference(resolution,[],[f125,f38])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f124,f51])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f123,f28])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f122,f27])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f121,f41])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f120,f40])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f118,f39])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK2,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK2) | k3_tmap_1(X0,sK1,sK2,X1,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X1))) )),
% 0.20/0.50    inference(resolution,[],[f47,f29])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k2_tmap_1(sK2,sK1,sK5,sK4))),
% 0.20/0.50    inference(backward_demodulation,[],[f30,f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4)),
% 0.20/0.50    inference(forward_demodulation,[],[f133,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    k2_tmap_1(sK2,sK1,sK5,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 0.20/0.50    inference(resolution,[],[f112,f88])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4))),
% 0.20/0.50    inference(resolution,[],[f132,f88])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~m1_pre_topc(sK4,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(superposition,[],[f48,f214])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))),
% 0.20/0.50    inference(subsumption_resolution,[],[f213,f64])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f212,f37])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    v2_struct_0(sK2) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f210,f79])).
% 0.20/0.50  fof(f210,plain,(
% 0.20/0.50    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) | ~l1_pre_topc(sK2)),
% 0.20/0.50    inference(resolution,[],[f201,f33])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X2,X3) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  % (2362)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (2377)------------------------------
% 0.20/0.50  % (2377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2377)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (2377)Memory used [KB]: 6396
% 0.20/0.50  % (2377)Time elapsed: 0.071 s
% 0.20/0.50  % (2377)------------------------------
% 0.20/0.50  % (2377)------------------------------
% 0.20/0.50  % (2365)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (2361)Success in time 0.142 s
%------------------------------------------------------------------------------
